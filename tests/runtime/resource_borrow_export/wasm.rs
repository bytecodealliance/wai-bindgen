wit_bindgen::generate!({
    path: "../../tests/runtime/resource_borrow_export",
});

use exports::test::resource_borrow_export::test::{Guest, GuestThing, ThingBorrow};

pub struct Test {}

export_resource_borrow_export!(Test);

pub struct MyThing {
    val: u32,
}

impl Guest for Test {
    type Thing = MyThing;

    fn foo(v: ThingBorrow<'_>) -> u32 {
        v.get::<MyThing>().val + 2
    }
}

impl GuestThing for MyThing {
    fn new(v: u32) -> Self {
        Self { val: v + 1 }
    }
}
