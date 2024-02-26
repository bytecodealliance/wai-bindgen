#![allow(unused_macros)]
#![allow(dead_code, unused_variables)]

mod codegen_tests {
    macro_rules! codegen_test {
        ($id:ident $name:tt $test:tt) => {
            mod $id {
                wit_bindgen::generate!({
                    path: $test,
                    stubs
                });

                // This empty module named 'core' is here to catch module path
                // conflicts with 'core' modules used in code generated by the
                // wit_bindgen::generate macro.
                // Ref: https://github.com/bytecodealliance/wit-bindgen/pull/568
                mod core {}

                #[test]
                fn works() {}

                mod borrowed {
                    wit_bindgen::generate!({
                        path: $test,
                        ownership: Borrowing {
                            duplicate_if_necessary: false
                        },
                        stubs,
                        export_prefix: "[borrowed]",
                    });

                    #[test]
                    fn works() {}
                }

                mod duplicate {
                    wit_bindgen::generate!({
                        path: $test,
                        ownership: Borrowing {
                            duplicate_if_necessary: true
                        },
                        stubs,
                        export_prefix: "[duplicate]",
                    });

                    #[test]
                    fn works() {}
                }
            }

        };
    }
    test_helpers::codegen_tests!();
}

mod strings {
    wit_bindgen::generate!({
        inline: "
            package my:strings;

            world not-used-name {
                import cat: interface {
                    foo: func(x: string);
                    bar: func() -> string;
                }
            }
        ",
    });

    #[allow(dead_code)]
    fn test() {
        // Test the argument is `&str`.
        cat::foo("hello");

        // Test the return type is `String`.
        let _t: String = cat::bar();
    }
}

/// Like `strings` but with raw_strings`.
mod raw_strings {
    wit_bindgen::generate!({
        inline: "
            package my:raw-strings;

            world not-used-name {
                import cat: interface {
                    foo: func(x: string);
                    bar: func() -> string;
                }
            }
        ",
        raw_strings,
    });

    #[allow(dead_code)]
    fn test() {
        // Test the argument is `&[u8]`.
        cat::foo(b"hello");

        // Test the return type is `Vec<u8>`.
        let _t: Vec<u8> = cat::bar();
    }
}

mod skip {
    wit_bindgen::generate!({
        inline: "
            package my:inline;

            world baz {
                export exports: interface {
                    foo: func();
                    bar: func();
                }
            }
        ",
        skip: ["foo"],
        exports: {
            "exports": Component
        }
    });

    struct Component;

    impl exports::exports::Guest for Component {
        fn bar() {}
    }
}

mod symbol_does_not_conflict {
    wit_bindgen::generate!({
        inline: "
            package my:inline;

            interface foo1 {
                foo: func();
            }

            interface foo2 {
                foo: func();
            }

            interface bar1 {
                bar: func() -> string;
            }

            interface bar2 {
                bar: func() -> string;
            }

            world foo {
                export foo1;
                export foo2;
                export bar1;
                export bar2;
            }
        ",
        exports: {
            "my:inline/foo1": Component,
            "my:inline/foo2": Component,
            "my:inline/bar1": Component,
            "my:inline/bar2": Component
        }
    });

    struct Component;

    impl exports::my::inline::foo1::Guest for Component {
        fn foo() {}
    }

    impl exports::my::inline::foo2::Guest for Component {
        fn foo() {}
    }

    impl exports::my::inline::bar1::Guest for Component {
        fn bar() -> String {
            String::new()
        }
    }

    impl exports::my::inline::bar2::Guest for Component {
        fn bar() -> String {
            String::new()
        }
    }
}

mod alternative_runtime_path {
    wit_bindgen::generate!({
        inline: "
            package my:inline;
            world foo {
                export foobar: func() -> string;
            }
        ",
        runtime_path: "my_rt",
        exports: {
            world: Component
        }
    });

    pub(crate) use wit_bindgen::rt as my_rt;

    struct Component;

    impl Guest for Component {
        fn foobar() -> String {
            String::new()
        }
    }
}

mod alternative_bitflags_path {
    wit_bindgen::generate!({
        inline: "
            package my:inline;
            world foo {
                flags bar {
                    foo,
                    bar,
                    baz
                }
                export get-flag: func() -> bar;
            }
        ",
        bitflags_path: "my_bitflags",
        exports: {
            world: Component
        }
    });

    pub(crate) use wit_bindgen::bitflags as my_bitflags;

    struct Component;

    impl Guest for Component {
        fn get_flag() -> Bar {
            Bar::BAZ
        }
    }
}

mod owned_resource_deref_mut {
    wit_bindgen::generate!({
        inline: "
            package my:inline;

            interface foo {
                resource bar {
                    constructor(data: u32);
                    get-data: func() -> u32;
                    consume: static func(%self: bar) -> u32;
                }
            }

            world baz {
                export foo;
            }
        ",
        exports: {
            "my:inline/foo/bar": Resource
        }
    });

    pub struct Resource {
        data: u32,
    }

    impl exports::my::inline::foo::GuestBar for Resource {
        fn new(data: u32) -> Self {
            Self { data }
        }

        fn get_data(&self) -> u32 {
            self.data
        }

        fn consume(mut this: exports::my::inline::foo::OwnBar) -> u32 {
            // Check that Deref<Target = Self> is implemented
            let prior_data: &u32 = &this.data;
            let new_data = prior_data + 1;
            // Check that DerefMut<Target = Self> is implemented
            let mutable_data: &mut u32 = &mut this.data;
            *mutable_data = new_data;
            this.data
        }
    }
}

mod package_with_versions {
    wit_bindgen::generate!({
        inline: "
            package my:inline@0.0.0;

            interface foo {
                resource bar {
                    constructor();
                }
            }

            world baz {
                export foo;
            }
        ",
        exports: {
            "my:inline/foo/bar": Resource
        }
    });

    pub struct Resource;

    impl exports::my::inline::foo::GuestBar for Resource {
        fn new() -> Self {
            loop {}
        }
    }
}

mod custom_derives {
    use std::collections::{hash_map::RandomState, HashSet};

    wit_bindgen::generate!({
        inline: "
            package my:inline;

            interface blah {
                record foo {
                    field1: string,
                    field2: list<u32>
                }

                bar: func(cool: foo);
            }

            world baz {
                export blah;
            }
        ",
        exports: {
            "my:inline/blah": Component
        },
        // Clone is included by default almost everywhere, so include it here to make sure it
        // doesn't conflict
        additional_derives: [serde::Serialize, serde::Deserialize, Hash, Clone, PartialEq, Eq],
    });

    use exports::my::inline::blah::Foo;

    struct Component;
    impl exports::my::inline::blah::Guest for Component {
        fn bar(cool: Foo) {
            // Check that built in derives that I've added actually work by seeing that this hashes
            let _blah: HashSet<Foo, RandomState> = HashSet::from_iter([Foo {
                field1: "hello".to_string(),
                field2: vec![1, 2, 3],
            }]);

            // Check that the attributes from an external crate actually work. If they don't work,
            // compilation will fail here
            let _ = serde_json::to_string(&cool);
        }
    }
}

mod with {
    wit_bindgen::generate!({
        inline: "
            package my:inline;

            interface foo {
                record msg {
                    field: string,
                }
            }

            interface bar {
                use foo.{msg};

                bar: func(m: msg);
            }

            world baz {
                import bar;
            }
        ",
        with: {
            "my:inline/foo": other::my::inline::foo,
        },
    });

    pub mod other {
        wit_bindgen::generate!({
            inline: "
                package my:inline;

                interface foo {
                    record msg {
                        field: string,
                    }
                }

                world dummy {
                    use foo.{msg};
                    import bar: func(m: msg);
                }
            ",
        });
    }

    #[allow(dead_code)]
    fn test() {
        let msg = other::my::inline::foo::Msg {
            field: "hello".to_string(),
        };
        my::inline::bar::bar(&msg);
    }
}

mod with_and_resources {
    wit_bindgen::generate!({
        inline: "
            package my:inline;

            interface foo {
                resource a;
            }

            interface bar {
                use foo.{a};

                bar: func(m: a) -> list<a>;
            }

            world baz {
                import bar;
            }
        ",
        with: {
            "my:inline/foo": other::my::inline::foo,
        },
    });

    pub mod other {
        wit_bindgen::generate!({
            inline: "
                package my:inline;

                interface foo {
                    resource a;
                }

                world dummy {
                    use foo.{a};
                    import bar: func(m: a);
                }
            ",
        });
    }
}
