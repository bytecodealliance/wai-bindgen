use heck::*;
use std::fmt;
use std::str::FromStr;
use wit_bindgen_core::abi::{Bitcast, WasmType};
use wit_bindgen_core::wit_parser::*;

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum TypeMode {
    Owned,
    AllBorrowed(&'static str),
    LeafBorrowed(&'static str),
    HandlesBorrowed(&'static str),
}

#[derive(Default, Debug, Clone, Copy)]
pub enum Ownership {
    /// Generated types will be composed entirely of owning fields, regardless
    /// of whether they are used as parameters to imports or not.
    #[default]
    Owning,

    /// Generated types used as parameters to imports will be "deeply
    /// borrowing", i.e. contain references rather than owned values when
    /// applicable.
    Borrowing {
        /// Whether or not to generate "duplicate" type definitions for a single
        /// WIT type if necessary, for example if it's used as both an import
        /// and an export, or if it's used both as a parameter to an import and
        /// a return value from an import.
        duplicate_if_necessary: bool,
    },
}

impl FromStr for Ownership {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "owning" => Ok(Self::Owning),
            "borrowing" => Ok(Self::Borrowing {
                duplicate_if_necessary: false,
            }),
            "borrowing-duplicate-if-necessary" => Ok(Self::Borrowing {
                duplicate_if_necessary: true,
            }),
            _ => Err(format!(
                "unrecognized ownership: `{s}`; \
                 expected `owning`, `borrowing`, or `borrowing-duplicate-if-necessary`"
            )),
        }
    }
}

impl fmt::Display for Ownership {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self {
            Ownership::Owning => "owning",
            Ownership::Borrowing {
                duplicate_if_necessary: false,
            } => "borrowing",
            Ownership::Borrowing {
                duplicate_if_necessary: true,
            } => "borrowing-duplicate-if-necessary",
        })
    }
}

#[derive(Default)]
pub struct FnSig {
    pub async_: bool,
    pub unsafe_: bool,
    pub private: bool,
    pub use_item_name: bool,
    pub generics: Option<String>,
    pub self_arg: Option<String>,
    pub self_is_first_param: bool,
}

pub fn to_rust_ident(name: &str) -> String {
    match name {
        // Escape Rust keywords.
        // Source: https://doc.rust-lang.org/reference/keywords.html
        "as" => "as_".into(),
        "break" => "break_".into(),
        "const" => "const_".into(),
        "continue" => "continue_".into(),
        "crate" => "crate_".into(),
        "else" => "else_".into(),
        "enum" => "enum_".into(),
        "extern" => "extern_".into(),
        "false" => "false_".into(),
        "fn" => "fn_".into(),
        "for" => "for_".into(),
        "if" => "if_".into(),
        "impl" => "impl_".into(),
        "in" => "in_".into(),
        "let" => "let_".into(),
        "loop" => "loop_".into(),
        "match" => "match_".into(),
        "mod" => "mod_".into(),
        "move" => "move_".into(),
        "mut" => "mut_".into(),
        "pub" => "pub_".into(),
        "ref" => "ref_".into(),
        "return" => "return_".into(),
        "self" => "self_".into(),
        "static" => "static_".into(),
        "struct" => "struct_".into(),
        "super" => "super_".into(),
        "trait" => "trait_".into(),
        "true" => "true_".into(),
        "type" => "type_".into(),
        "unsafe" => "unsafe_".into(),
        "use" => "use_".into(),
        "where" => "where_".into(),
        "while" => "while_".into(),
        "async" => "async_".into(),
        "await" => "await_".into(),
        "dyn" => "dyn_".into(),
        "abstract" => "abstract_".into(),
        "become" => "become_".into(),
        "box" => "box_".into(),
        "do" => "do_".into(),
        "final" => "final_".into(),
        "macro" => "macro_".into(),
        "override" => "override_".into(),
        "priv" => "priv_".into(),
        "typeof" => "typeof_".into(),
        "unsized" => "unsized_".into(),
        "virtual" => "virtual_".into(),
        "yield" => "yield_".into(),
        "try" => "try_".into(),
        s => s.to_snake_case(),
    }
}

pub fn to_upper_camel_case(name: &str) -> String {
    match name {
        // The name "Guest" is reserved for traits generated by exported
        // interfaces, so remap types defined in wit to something else.
        "guest" => "Guest_".to_string(),
        s => s.to_upper_camel_case(),
    }
}

pub fn wasm_type(ty: WasmType) -> &'static str {
    match ty {
        WasmType::I32 => "i32",
        WasmType::I64 => "i64",
        WasmType::F32 => "f32",
        WasmType::F64 => "f64",
    }
}

pub fn int_repr(repr: Int) -> &'static str {
    match repr {
        Int::U8 => "u8",
        Int::U16 => "u16",
        Int::U32 => "u32",
        Int::U64 => "u64",
    }
}

pub fn bitcast(casts: &[Bitcast], operands: &[String], results: &mut Vec<String>) {
    for (cast, operand) in casts.iter().zip(operands) {
        results.push(match cast {
            Bitcast::None => operand.clone(),
            Bitcast::I32ToI64 => format!("i64::from({})", operand),
            Bitcast::F32ToI32 => format!("({}).to_bits() as i32", operand),
            Bitcast::F64ToI64 => format!("({}).to_bits() as i64", operand),
            Bitcast::I64ToI32 => format!("{} as i32", operand),
            Bitcast::I32ToF32 => format!("f32::from_bits({} as u32)", operand),
            Bitcast::I64ToF64 => format!("f64::from_bits({} as u64)", operand),
            Bitcast::F32ToI64 => format!("i64::from(({}).to_bits())", operand),
            Bitcast::I64ToF32 => format!("f32::from_bits({} as u32)", operand),
        });
    }
}

pub enum RustFlagsRepr {
    U8,
    U16,
    U32,
    U64,
    U128,
}

impl RustFlagsRepr {
    pub fn new(f: &Flags) -> RustFlagsRepr {
        match f.repr() {
            FlagsRepr::U8 => RustFlagsRepr::U8,
            FlagsRepr::U16 => RustFlagsRepr::U16,
            FlagsRepr::U32(1) => RustFlagsRepr::U32,
            FlagsRepr::U32(2) => RustFlagsRepr::U64,
            FlagsRepr::U32(3 | 4) => RustFlagsRepr::U128,
            FlagsRepr::U32(n) => panic!("unsupported number of flags: {}", n * 32),
        }
    }
}

impl fmt::Display for RustFlagsRepr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RustFlagsRepr::U8 => "u8".fmt(f),
            RustFlagsRepr::U16 => "u16".fmt(f),
            RustFlagsRepr::U32 => "u32".fmt(f),
            RustFlagsRepr::U64 => "u64".fmt(f),
            RustFlagsRepr::U128 => "u128".fmt(f),
        }
    }
}

pub fn dealias(resolve: &Resolve, mut id: TypeId) -> TypeId {
    loop {
        match &resolve.types[id].kind {
            TypeDefKind::Type(Type::Id(that_id)) => id = *that_id,
            _ => break id,
        }
    }
}
