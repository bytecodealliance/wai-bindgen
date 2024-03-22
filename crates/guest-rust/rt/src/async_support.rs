#![deny(missing_docs)]
#![allow(static_mut_refs)]

extern crate std;

use {
    futures::{
        channel::oneshot,
        future::FutureExt,
        stream::{FuturesUnordered, StreamExt},
    },
    once_cell::sync::Lazy,
    std::{
        alloc::{self, Layout},
        any::Any,
        boxed::Box,
        collections::hash_map,
        collections::HashMap,
        fmt::{self, Debug, Display},
        future::Future,
        pin::Pin,
        ptr,
        sync::Arc,
        task::{Context, Poll, Wake, Waker},
        vec::Vec,
    },
};

pub use futures;

type BoxFuture = Pin<Box<dyn Future<Output = ()> + 'static>>;

/// Represents a task created by either a call to an async-lifted export or a
/// future run using `block_on` or `poll_future`.
struct FutureState {
    /// Number of in-progress async-lowered import calls and/or stream/future reads/writes.
    todo: usize,
    /// Remaining work to do (if any) before this task can be considered "done".
    ///
    /// Note that we won't tell the host the task is done until this is drained
    /// and `todo` is zero.
    tasks: Option<FuturesUnordered<BoxFuture>>,
}

/// Represents the state of a stream or future.
#[doc(hidden)]
pub enum Handle {
    LocalOpen,
    LocalReady(Box<dyn Any>, Waker),
    LocalWaiting(oneshot::Sender<Box<dyn Any>>),
    LocalClosed,
    Read,
    Write,
}

/// The current task being polled (or null if none).
static mut CURRENT: *mut FutureState = ptr::null_mut();

/// Map of any in-progress calls to async-lowered imports, keyed by the
/// identifiers issued by the host.
static mut CALLS: Lazy<HashMap<i32, oneshot::Sender<u32>>> = Lazy::new(HashMap::new);

/// Any newly-deferred work queued by calls to the `spawn` function while
/// polling the current task.
static mut SPAWNED: Vec<BoxFuture> = Vec::new();

/// The states of all currently-open streams and futures.
static mut HANDLES: Lazy<HashMap<u32, Handle>> = Lazy::new(HashMap::new);

#[doc(hidden)]
pub fn with_entry<T>(handle: u32, fun: impl FnOnce(hash_map::Entry<'_, u32, Handle>) -> T) -> T {
    fun(unsafe { HANDLES.entry(handle) })
}

fn dummy_waker() -> Waker {
    struct DummyWaker;

    impl Wake for DummyWaker {
        fn wake(self: Arc<Self>) {}
    }

    static WAKER: Lazy<Arc<DummyWaker>> = Lazy::new(|| Arc::new(DummyWaker));

    WAKER.clone().into()
}

/// Poll the specified task until it either completes or can't make immediate
/// progress.
unsafe fn poll(state: *mut FutureState) -> Poll<()> {
    loop {
        if let Some(futures) = (*state).tasks.as_mut() {
            CURRENT = state;
            let poll = futures.poll_next_unpin(&mut Context::from_waker(&dummy_waker()));
            CURRENT = ptr::null_mut();

            if SPAWNED.is_empty() {
                match poll {
                    Poll::Ready(Some(())) => (),
                    Poll::Ready(None) => {
                        (*state).tasks = None;
                        break Poll::Ready(());
                    }
                    Poll::Pending => break Poll::Pending,
                }
            } else {
                futures.extend(SPAWNED.drain(..));
            }
        } else {
            break Poll::Ready(());
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
) -> *mut u8 {
    let state = Box::into_raw(Box::new(FutureState {
        todo: 0,
        tasks: Some(
            [Box::pin(future.map(fun)) as BoxFuture]
                .into_iter()
                .collect(),
        ),
    }));
    match unsafe { poll(state) } {
        Poll::Ready(()) => ptr::null_mut(),
        Poll::Pending => state as _,
    }
}

/// Await the completion of a call to an async-lowered import.
#[doc(hidden)]
pub async unsafe fn await_result(
    import: unsafe extern "C" fn(*mut u8, *mut u8) -> i32,
    params_layout: Layout,
    params: *mut u8,
    results: *mut u8,
) {
    const STATUS_STARTING: u32 = 0;
    const STATUS_STARTED: u32 = 1;
    const STATUS_RETURNED: u32 = 2;
    const STATUS_DONE: u32 = 3;

    let result = import(params, results) as u32;
    let status = result >> 30;
    let call = (result & !(0b11 << 30)) as i32;

    if status != STATUS_DONE {
        assert!(!CURRENT.is_null());
        (*CURRENT).todo += 1;
    }

    match status {
        STATUS_STARTING => {
            let (tx, rx) = oneshot::channel();
            CALLS.insert(call, tx);
            rx.await.unwrap();
            alloc::dealloc(params, params_layout);
        }
        STATUS_STARTED => {
            alloc::dealloc(params, params_layout);
            let (tx, rx) = oneshot::channel();
            CALLS.insert(call, tx);
            rx.await.unwrap();
        }
        STATUS_RETURNED | STATUS_DONE => {
            alloc::dealloc(params, params_layout);
        }
        _ => unreachable!(),
    }
}

/// stream/future read/write results defined by the Component Model ABI.
mod results {
    pub const BLOCKED: u32 = 0xffff_ffff;
    pub const CLOSED: u32 = 0x8000_0000;
    pub const CANCELED: u32 = 0;
}

/// Await the completion of a future read or write.
#[doc(hidden)]
pub async unsafe fn await_future_result(
    import: unsafe extern "C" fn(u32, *mut u8) -> u32,
    future: u32,
    address: *mut u8,
) -> bool {
    let result = import(future, address);
    match result {
        results::BLOCKED => {
            assert!(!CURRENT.is_null());
            (*CURRENT).todo += 1;
            let (tx, rx) = oneshot::channel();
            CALLS.insert(future as _, tx);
            let v = rx.await.unwrap();
            v == 1
        }
        results::CLOSED | results::CANCELED => false,
        1 => true,
        _ => unreachable!(),
    }
}

/// Await the completion of a stream read or write.
#[doc(hidden)]
pub async unsafe fn await_stream_result(
    import: unsafe extern "C" fn(u32, *mut u8, u32) -> u32,
    stream: u32,
    address: *mut u8,
    count: u32,
) -> Option<usize> {
    let result = import(stream, address, count);
    match result {
        results::BLOCKED => {
            assert!(!CURRENT.is_null());
            (*CURRENT).todo += 1;
            let (tx, rx) = oneshot::channel();
            CALLS.insert(stream as _, tx);
            let v = rx.await.unwrap();
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

/// Call the `subtask.drop` canonical built-in function.
fn subtask_drop(subtask: u32) {
    #[cfg(not(target_arch = "wasm32"))]
    {
        _ = subtask;
        unreachable!();
    }

    #[cfg(target_arch = "wasm32")]
    {
        #[link(wasm_import_module = "$root")]
        extern "C" {
            #[link_name = "[subtask-drop]"]
            fn subtask_drop(_: u32);
        }
        unsafe {
            subtask_drop(subtask);
        }
    }
}

/// Handle a progress notification from the host regarding either a call to an
/// async-lowered import or a stream/future read/write operation.
#[doc(hidden)]
pub unsafe fn callback(ctx: *mut u8, event0: i32, event1: i32, event2: i32) -> i32 {
    const _EVENT_CALL_STARTING: i32 = 0;
    const EVENT_CALL_STARTED: i32 = 1;
    const EVENT_CALL_RETURNED: i32 = 2;
    const EVENT_CALL_DONE: i32 = 3;
    const _EVENT_YIELDED: i32 = 4;
    const EVENT_STREAM_READ: i32 = 5;
    const EVENT_STREAM_WRITE: i32 = 6;
    const EVENT_FUTURE_READ: i32 = 7;
    const EVENT_FUTURE_WRITE: i32 = 8;

    match event0 {
        EVENT_CALL_STARTED => 0,
        EVENT_CALL_RETURNED | EVENT_CALL_DONE | EVENT_STREAM_READ | EVENT_STREAM_WRITE
        | EVENT_FUTURE_READ | EVENT_FUTURE_WRITE => {
            if let Some(call) = CALLS.remove(&event1) {
                _ = call.send(event2 as _);
            }

            let state = ctx as *mut FutureState;
            let done = poll(state).is_ready();

            if event0 == EVENT_CALL_DONE {
                subtask_drop(event1 as u32);
            }

            if matches!(
                event0,
                EVENT_CALL_DONE
                    | EVENT_STREAM_READ
                    | EVENT_STREAM_WRITE
                    | EVENT_FUTURE_READ
                    | EVENT_FUTURE_WRITE
            ) {
                (*state).todo -= 1;
            }

            if done && (*state).todo == 0 {
                drop(Box::from_raw(state));
                1
            } else {
                0
            }
        }
        _ => unreachable!(),
    }
}

/// Represents the Component Model `error-context` type.
pub struct ErrorContext {
    handle: u32,
}

impl ErrorContext {
    #[doc(hidden)]
    pub fn from_handle(handle: u32) -> Self {
        Self { handle }
    }

    #[doc(hidden)]
    pub fn handle(&self) -> u32 {
        self.handle
    }
}

impl Debug for ErrorContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ErrorContext").finish()
    }
}

impl Display for ErrorContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Error")
    }
}

impl std::error::Error for ErrorContext {}

impl Drop for ErrorContext {
    fn drop(&mut self) {
        #[cfg(not(target_arch = "wasm32"))]
        {
            unreachable!();
        }

        #[cfg(target_arch = "wasm32")]
        {
            #[link(wasm_import_module = "$root")]
            extern "C" {
                #[link_name = "[error-context-drop]"]
                fn error_drop(_: u32);
            }
            if self.handle != 0 {
                unsafe { error_drop(self.handle) }
            }
        }
    }
}

/// Defer the specified future to be run after the current async-lifted export
/// task has returned a value.
///
/// The task will remain in a running state until all spawned futures have
/// completed.
pub fn spawn(future: impl Future<Output = ()> + 'static) {
    unsafe { SPAWNED.push(Box::pin(future)) }
}

fn task_wait(state: &mut FutureState) {
    #[cfg(not(target_arch = "wasm32"))]
    {
        _ = state;
        unreachable!();
    }

    #[cfg(target_arch = "wasm32")]
    {
        #[link(wasm_import_module = "$root")]
        extern "C" {
            #[link_name = "[task-wait]"]
            fn wait(_: *mut i32) -> i32;
        }
        let mut payload = [0i32; 2];
        unsafe {
            let event0 = wait(payload.as_mut_ptr());
            callback(state as *mut _ as _, event0, payload[0], payload[1]);
        }
    }
}

/// Run the specified future to completion, returning the result.
///
/// This uses `task.wait` to poll for progress on any in-progress calls to
/// async-lowered imports as necessary.
// TODO: refactor so `'static` bounds aren't necessary
pub fn block_on<T: 'static>(future: impl Future<Output = T> + 'static) -> T {
    let (tx, mut rx) = oneshot::channel();
    let state = &mut FutureState {
        todo: 0,
        tasks: Some(
            [Box::pin(future.map(move |v| drop(tx.send(v)))) as BoxFuture]
                .into_iter()
                .collect(),
        ),
    };
    loop {
        match unsafe { poll(state) } {
            Poll::Ready(()) => break rx.try_recv().unwrap().unwrap(),
            Poll::Pending => task_wait(state),
        }
    }
}

/// Call the `task.yield` canonical built-in function.
///
/// This yields control to the host temporarily, allowing other tasks to make
/// progress.  It's a good idea to call this inside a busy loop which does not
/// otherwise ever yield control the the host.
pub fn task_yield() {
    #[cfg(not(target_arch = "wasm32"))]
    {
        unreachable!();
    }

    #[cfg(target_arch = "wasm32")]
    {
        #[link(wasm_import_module = "$root")]
        extern "C" {
            #[link_name = "[task-yield]"]
            fn yield_();
        }
        unsafe {
            yield_();
        }
    }
}

/// Call the `task.backpressure` canonical built-in function.
///
/// When `enabled` is `true`, this tells the host to defer any new calls to this
/// component instance until further notice (i.e. until `task.backpressure` is
/// called again with `enabled` set to `false`).
pub fn task_backpressure(enabled: bool) {
    #[cfg(not(target_arch = "wasm32"))]
    {
        _ = enabled;
        unreachable!();
    }

    #[cfg(target_arch = "wasm32")]
    {
        #[link(wasm_import_module = "$root")]
        extern "C" {
            #[link_name = "[task-backpressure]"]
            fn backpressure(_: i32);
        }
        unsafe {
            backpressure(if enabled { 1 } else { 0 });
        }
    }
}
