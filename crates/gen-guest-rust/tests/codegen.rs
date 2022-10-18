#![allow(unused_macros)]

mod exports {
    macro_rules! codegen_test {
        ($name:ident $test:tt) => {
            mod $name {
                wit_bindgen_guest_rust::generate!({
                    export: $test,
                    name: "not-used-name",
                });

                mod default {
                    wit_bindgen_guest_rust::generate!({
                        default: $test,
                        name: "the-world-name",
                    });

                    #[test]
                    fn $name() {}
                }
            }

            #[test]
            fn $name() {}
        };
    }
    test_helpers::codegen_tests!("*.wit");
}

mod imports {
    macro_rules! codegen_test {
        ($name:ident $test:tt) => {
            wit_bindgen_guest_rust::generate!({
                import: $test,
                name: "not-used-name",
            });

            #[test]
            fn $name() {}
        };
    }
    test_helpers::codegen_tests!("*.wit");

    mod unchecked {
        macro_rules! codegen_test {
            ($name:ident $test:tt) => {
                wit_bindgen_guest_rust::generate!({
                    import: $test,
                    unchecked,
                    name: "not-used-name",
                });

                #[test]
                fn $name() {}
            };
        }
        test_helpers::codegen_tests!("*.wit");
    }
}

mod altogether {
    macro_rules! codegen_test {
        ($name:ident $test:tt) => {
            mod $name {
                wit_bindgen_guest_rust::generate!({
                    // rename the input `*.wit` file for imports/exports to
                    // avoid having them having the same name which the rust
                    // generator currently doesn't support.
                    import["the-import"]: $test,
                    export["the-export"]: $test,
                    default: $test,
                    unchecked,
                    name: "not-used-name",
                });

                #[test]
                fn works() {}
            }
        };
    }
    test_helpers::codegen_tests!("*.wit");
}

mod strings {
    wit_bindgen_guest_rust::generate!({
        import_str["cat"]: "
            foo: func(x: string)
            bar: func() -> string
        ",
        name: "not-used-name",
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
    wit_bindgen_guest_rust::generate!({
        import_str["cat"]: "
            foo: func(x: string)
            bar: func() -> string
        ",
        raw_strings,
        name: "not-used-name",
    });

    #[allow(dead_code)]
    fn test() {
        // Test the argument is `&[u8]`.
        cat::foo(b"hello");

        // Test the return type is `Vec<u8>`.
        let _t: Vec<u8> = cat::bar();
    }
}
