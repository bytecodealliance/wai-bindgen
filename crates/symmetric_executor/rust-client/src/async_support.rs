use futures::{task::Waker, FutureExt};
use std::{
    future::Future,
    pin::Pin,
    task::{Context, Poll, RawWaker, RawWakerVTable},
};

use crate::{
    module::symmetric::runtime::symmetric_executor::{
        self, CallbackState, EventGenerator, EventSubscription,
    },
    subscribe_event_send_ptr,
};

pub use stream_support::{results, Stream, StreamHandle2, StreamReader, StreamWriter};

// pub use futures;

mod future_support;
// later make it non-pub
pub mod stream_support;

// See https://github.com/rust-lang/rust/issues/13231 for the limitation
// / Send constraint on futures for spawn, loosen later
// pub unsafe auto trait MaybeSend : Send {}
// unsafe impl<T> MaybeSend for T where T: Send {}

type BoxFuture = Pin<Box<dyn Future<Output = ()> + 'static>>;

struct FutureState {
    future: BoxFuture,
    // signal to activate once the current async future has finished
    completion_event: Option<EventGenerator>,
    // the event this future should wake on
    waiting_for: Option<EventSubscription>,
}

static VTABLE: RawWakerVTable = RawWakerVTable::new(
    |_| RawWaker::new(core::ptr::null(), &VTABLE),
    // `wake` does nothing
    |_| {},
    // `wake_by_ref` does nothing
    |_| {},
    // Dropping does nothing as we don't allocate anything
    |_| {},
);

pub fn new_waker(waiting_for_ptr: *mut Option<EventSubscription>) -> Waker {
    unsafe { Waker::from_raw(RawWaker::new(waiting_for_ptr.cast(), &VTABLE)) }
}

unsafe fn poll(state: *mut FutureState) -> Poll<()> {
    let mut pinned = std::pin::pin!(&mut (*state).future);
    let waker = new_waker(&mut (&mut *state).waiting_for as *mut Option<EventSubscription>);
    pinned
        .as_mut()
        .poll(&mut Context::from_waker(&waker))
        .map(|()| {
            let state_owned = Box::from_raw(state);
            if let Some(waker) = &state_owned.completion_event {
                waker.activate();
            }
            drop(state_owned);
        })
}

pub async fn wait_on(wait_for: EventSubscription) {
    std::future::poll_fn(move |cx| {
        if wait_for.ready() {
            Poll::Ready(())
        } else {
            // remember this eventsubscription in the context
            let data = cx.waker().data();
            let mut copy = Some(wait_for.dup());
            std::mem::swap(
                unsafe { &mut *(data.cast::<Option<EventSubscription>>().cast_mut()) },
                &mut copy,
            );
            Poll::Pending
        }
    })
    .await
}

extern "C" fn symmetric_callback(obj: *mut ()) -> symmetric_executor::CallbackState {
    match unsafe { poll(obj.cast()) } {
        Poll::Ready(_) => CallbackState::Ready,
        Poll::Pending => {
            let state = obj.cast::<FutureState>();
            let waiting_for = unsafe { &mut *state }.waiting_for.take();
            super::register(waiting_for.unwrap(), symmetric_callback, obj);
            // as we registered this callback on a new event stop calling
            // from the old event
            CallbackState::Ready
        }
    }
}

/// Poll the future generated by a call to an async-lifted export once, calling
/// the specified closure (presumably backed by a call to `task.return`) when it
/// generates a value.
///
/// This will return a non-null pointer representing the task if it hasn't
/// completed immediately; otherwise it returns null.
#[doc(hidden)]
pub fn first_poll<T: 'static>(
    future: impl Future<Output = T> + 'static,
    fun: impl FnOnce(T) + 'static,
) -> *mut () {
    let state = Box::into_raw(Box::new(FutureState {
        future: Box::pin(future.map(fun)),
        completion_event: None,
        waiting_for: None,
    }));
    match unsafe { poll(state) } {
        Poll::Ready(()) => core::ptr::null_mut(),
        Poll::Pending => {
            let completion_event = EventGenerator::new();
            let wait_chain = completion_event.subscribe().take_handle() as *mut ();
            unsafe { &mut *state }
                .completion_event
                .replace(completion_event);
            let waiting_for = unsafe { &mut *state }.waiting_for.take();
            super::register(waiting_for.unwrap(), symmetric_callback, state.cast());
            wait_chain
        }
    }
}

/// Await the completion of a call to an async-lowered import.
#[doc(hidden)]
pub async unsafe fn await_result(function: impl Fn() -> *mut u8) {
    let wait_for = function();
    if !wait_for.is_null() {
        let wait_for = unsafe { EventSubscription::from_handle(wait_for as usize) };
        wait_on(wait_for).await;
    }
}

pub fn spawn(future: impl Future<Output = ()> + 'static + Send) {
    let wait_for = first_poll(future, |()| ());
    let wait_for = unsafe { EventSubscription::from_handle(wait_for as usize) };
    drop(wait_for);
}

#[repr(transparent)]
pub struct AddressSend(pub *mut ());
unsafe impl Send for AddressSend {}
// unsafe impl Sync for StreamHandle2 {}

// this is used for reading?
pub async unsafe fn await_stream_result(
    import: unsafe extern "C" fn(*mut Stream, *mut (), usize) -> isize,
    stream: StreamHandle2,
    address: AddressSend,
    count: usize,
) -> Option<usize> {
    let stream_copy = stream.0;
    let result = import(stream_copy, address.0, count);
    match result {
        results::BLOCKED => {
            let event =
                unsafe { subscribe_event_send_ptr(stream_support::read_ready_event(stream.0)) };
            event.reset();
            wait_on(event).await;
            let v = stream_support::read_amount(stream.0);
            if let results::CLOSED | results::CANCELED = v {
                None
            } else {
                Some(usize::try_from(v).unwrap())
            }
        }
        results::CLOSED | results::CANCELED => None,
        v => Some(usize::try_from(v).unwrap()),
    }
}
