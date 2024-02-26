wit_bindgen::generate!({
    path: "../../tests/runtime/resource_into_inner",
});

use exports::test::resource_into_inner::test::{Guest, GuestThing, Thing};

pub struct Test;

export_resource_into_inner!(Test);

impl Guest for Test {
    type Thing = MyThing;

    fn test() {
        let text = "Jabberwocky";
        let thing = Thing::new(MyThing(text.to_string()));
        let inner: MyThing = thing.into_inner();
        assert_eq!(text, &inner.0);
    }
}

pub struct MyThing(String);

impl GuestThing for MyThing {
    fn new(text: String) -> Self {
        Self(text)
    }
}
