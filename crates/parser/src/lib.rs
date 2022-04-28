use anyhow::{anyhow, bail, Context, Result};
use id_arena::{Arena, Id};
use pulldown_cmark::{CodeBlockKind, CowStr, Event, Options, Parser, Tag};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};

pub mod abi;
mod ast;
mod sizealign;
pub use sizealign::*;

/// Checks if the given string is a legal identifier in wit.
pub fn validate_id(s: &str) -> Result<()> {
    ast::validate_id(0, s)?;
    Ok(())
}

#[derive(Debug, Default)]
pub struct Interface {
    pub name: String,
    pub types: Arena<TypeDef>,
    pub type_lookup: HashMap<String, TypeId>,
    pub resources: Arena<Resource>,
    pub resource_lookup: HashMap<String, ResourceId>,
    pub interfaces: Arena<Interface>,
    pub interface_lookup: HashMap<String, InterfaceId>,
    pub functions: Vec<Function>,
    pub globals: Vec<Global>,
}

pub type TypeId = Id<TypeDef>;
pub type ResourceId = Id<Resource>;
pub type InterfaceId = Id<Interface>;

#[derive(Debug)]
pub struct TypeDef {
    pub docs: Docs,
    pub kind: TypeDefKind,
    pub name: Option<String>,
    /// `None` if this type is originally declared in this instance or
    /// otherwise `Some` if it was originally defined in a different module.
    pub foreign_module: Option<String>,
}

#[derive(Debug)]
pub enum TypeDefKind {
    Record(Record),
    Flags(Flags),
    Variant(Variant),
    List(Type),
    Type(Type),
}

#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub enum Type {
    Unit,
    Bool,
    U8,
    U16,
    U32,
    U64,
    S8,
    S16,
    S32,
    S64,
    Float32,
    Float64,
    Char,
    String,
    Handle(ResourceId),
    Id(TypeId),
}

#[derive(PartialEq, Debug, Copy, Clone)]
pub enum Int {
    U8,
    U16,
    U32,
    U64,
}

#[derive(Debug)]
pub struct Record {
    pub fields: Vec<Field>,
    pub kind: RecordKind,
}

#[derive(Copy, Clone, Debug)]
pub enum RecordKind {
    Other,
    Tuple,
}

#[derive(Debug)]
pub struct Field {
    pub docs: Docs,
    pub name: String,
    pub ty: Type,
}

impl Record {
    pub fn is_tuple(&self) -> bool {
        matches!(self.kind, RecordKind::Tuple)
    }
}

impl RecordKind {
    fn infer(fields: &[Field]) -> RecordKind {
        if fields.is_empty() {
            return RecordKind::Other;
        }

        // fields with consecutive integer names get represented as tuples.
        if fields
            .iter()
            .enumerate()
            .all(|(i, m)| m.name.as_str().parse().ok() == Some(i))
        {
            return RecordKind::Tuple;
        }

        return RecordKind::Other;
    }
}

#[derive(Debug, Clone)]
pub struct Flags {
    pub flags: Vec<Flag>,
}

#[derive(Debug, Clone)]
pub struct Flag {
    pub docs: Docs,
    pub name: String,
}

#[derive(Debug)]
pub enum FlagsRepr {
    U8,
    U16,
    U32(usize),
}

impl Flags {
    pub fn repr(&self) -> FlagsRepr {
        match self.flags.len() {
            n if n <= 8 => FlagsRepr::U8,
            n if n <= 16 => FlagsRepr::U16,
            n => FlagsRepr::U32(sizealign::align_to(n, 32) / 32),
        }
    }
}

impl FlagsRepr {
    pub fn count(&self) -> usize {
        match self {
            FlagsRepr::U8 => 1,
            FlagsRepr::U16 => 1,
            FlagsRepr::U32(n) => *n,
        }
    }
}

#[derive(Debug)]
pub struct Variant {
    pub cases: Vec<Case>,
    /// The bit representation of the width of this variant's tag when the
    /// variant is stored in memory.
    pub tag: Int,
}

#[derive(Debug)]
pub struct Case {
    pub docs: Docs,
    pub name: String,
    pub ty: Option<Type>,
}

impl Variant {
    pub fn infer_tag(cases: usize) -> Int {
        match cases {
            n if n <= u8::max_value() as usize => Int::U8,
            n if n <= u16::max_value() as usize => Int::U16,
            n if n <= u32::max_value() as usize => Int::U32,
            n if n <= u64::max_value() as usize => Int::U64,
            _ => panic!("too many cases to fit in a repr"),
        }
    }

    pub fn is_enum(&self) -> bool {
        self.cases.iter().all(|c| c.ty.is_none())
    }

    pub fn is_union(&self) -> bool {
        self.cases
            .iter()
            .enumerate()
            .all(|(i, c)| c.name.parse().ok() == Some(i) && c.ty.is_some())
    }

    pub fn as_option(&self) -> Option<&Type> {
        if self.cases.len() != 2 {
            return None;
        }
        if self.cases[0].name != "none" || self.cases[0].ty.is_some() {
            return None;
        }
        if self.cases[1].name != "some" {
            return None;
        }
        self.cases[1].ty.as_ref()
    }

    pub fn as_expected(&self) -> Option<(Option<&Type>, Option<&Type>)> {
        if self.cases.len() != 2 {
            return None;
        }
        if self.cases[0].name != "ok" {
            return None;
        }
        if self.cases[1].name != "err" {
            return None;
        }
        Some((self.cases[0].ty.as_ref(), self.cases[1].ty.as_ref()))
    }
}

#[derive(Clone, Default, Debug)]
pub struct Docs {
    pub contents: Option<String>,
}

#[derive(Debug)]
pub struct Resource {
    pub docs: Docs,
    pub name: String,
    /// `None` if this resource is defined within the containing instance,
    /// otherwise `Some` if it's defined in an instance named here.
    pub foreign_module: Option<String>,
}

#[derive(Debug)]
pub struct Global {
    pub docs: Docs,
    pub name: String,
    pub ty: Type,
}

#[derive(Debug)]
pub struct Function {
    pub is_async: bool,
    pub docs: Docs,
    pub name: String,
    pub kind: FunctionKind,
    pub params: Vec<(String, Type)>,
    pub result: Type,
}

#[derive(Debug)]
pub enum FunctionKind {
    Freestanding,
    Static { resource: ResourceId, name: String },
    Method { resource: ResourceId, name: String },
}

impl Function {
    pub fn item_name(&self) -> &str {
        match &self.kind {
            FunctionKind::Freestanding => &self.name,
            FunctionKind::Static { name, .. } => name,
            FunctionKind::Method { name, .. } => name,
        }
    }
}

fn unwrap_md(contents: &str) -> String {
    let mut wit = String::new();
    let mut last_pos = 0;
    let mut in_wit_code_block = false;
    Parser::new_ext(contents, Options::empty())
        .into_offset_iter()
        .for_each(|(event, range)| match (event, range) {
            (Event::Start(Tag::CodeBlock(CodeBlockKind::Fenced(CowStr::Borrowed("wit")))), _) => {
                in_wit_code_block = true;
            }
            (Event::Text(text), range) if in_wit_code_block => {
                // Ensure that offsets are correct by inserting newlines to
                // cover the Markdown content outside of wit code blocks.
                for _ in contents[last_pos..range.start].lines() {
                    wit.push_str("\n");
                }
                wit.push_str(&text);
                last_pos = range.end;
            }
            (Event::End(Tag::CodeBlock(CodeBlockKind::Fenced(CowStr::Borrowed("wit")))), _) => {
                in_wit_code_block = false;
            }
            _ => {}
        });
    wit
}

impl Interface {
    pub fn parse(name: &str, input: &str) -> Result<Interface> {
        Interface::parse_with(name, input, |f| {
            Err(anyhow!("cannot load submodule `{}`", f))
        })
    }

    pub fn parse_file(path: impl AsRef<Path>) -> Result<Interface> {
        let path = path.as_ref();
        let parent = path.parent().unwrap();
        let contents = std::fs::read_to_string(&path)
            .with_context(|| format!("failed to read: {}", path.display()))?;
        Interface::parse_with(path, &contents, |path| load_fs(parent, path))
    }

    pub fn parse_with(
        filename: impl AsRef<Path>,
        contents: &str,
        mut load: impl FnMut(&str) -> Result<(PathBuf, String)>,
    ) -> Result<Interface> {
        Interface::_parse_with(
            filename.as_ref(),
            contents,
            &mut load,
            &mut HashSet::new(),
            &mut HashMap::new(),
        )
    }

    fn _parse_with(
        filename: &Path,
        contents: &str,
        load: &mut dyn FnMut(&str) -> Result<(PathBuf, String)>,
        visiting: &mut HashSet<PathBuf>,
        map: &mut HashMap<String, Interface>,
    ) -> Result<Interface> {
        let mut name = filename.file_stem().unwrap();
        let mut contents = contents;

        // If we have a ".md" file, it's a wit file wrapped in a markdown file;
        // parse the markdown to extract the `wit` code blocks.
        let md_contents;
        if filename.extension().and_then(|s| s.to_str()) == Some("md") {
            md_contents = unwrap_md(contents);
            contents = &md_contents[..];

            // Also strip the inner ".wit" extension.
            name = Path::new(name).file_stem().unwrap();
        }

        // Parse the `contents `into an AST
        let ast = match ast::Ast::parse(contents) {
            Ok(ast) => ast,
            Err(mut e) => {
                let file = filename.display().to_string();
                ast::rewrite_error(&mut e, &file, contents);
                return Err(e);
            }
        };

        // Load up any modules into our `map` that have not yet been parsed.
        if !visiting.insert(filename.to_path_buf()) {
            bail!("file `{}` recursively imports itself", filename.display())
        }
        for item in ast.items.iter() {
            let u = match item {
                ast::Item::Use(u) => u,
                _ => continue,
            };
            if map.contains_key(&*u.from[0].name) {
                continue;
            }
            let (filename, contents) = load(&u.from[0].name)
                // TODO: insert context here about `u.name.span` and `filename`
                ?;
            let instance = Interface::_parse_with(&filename, &contents, load, visiting, map)?;
            map.insert(u.from[0].name.to_string(), instance);
        }
        visiting.remove(filename);

        // and finally resolve everything into our final instance
        match ast.resolve(name.to_str().unwrap(), map) {
            Ok(i) => Ok(i),
            Err(mut e) => {
                let file = filename.display().to_string();
                ast::rewrite_error(&mut e, &file, contents);
                Err(e)
            }
        }
    }

    pub fn topological_types(&self) -> Vec<TypeId> {
        let mut ret = Vec::new();
        let mut visited = HashSet::new();
        for (id, _) in self.types.iter() {
            self.topo_visit(id, &mut ret, &mut visited);
        }
        ret
    }

    fn topo_visit(&self, id: TypeId, list: &mut Vec<TypeId>, visited: &mut HashSet<TypeId>) {
        if !visited.insert(id) {
            return;
        }
        match &self.types[id].kind {
            TypeDefKind::Flags(_) => {}
            TypeDefKind::Type(t) | TypeDefKind::List(t) => self.topo_visit_ty(t, list, visited),
            TypeDefKind::Record(r) => {
                for f in r.fields.iter() {
                    self.topo_visit_ty(&f.ty, list, visited);
                }
            }
            TypeDefKind::Variant(v) => {
                for v in v.cases.iter() {
                    if let Some(ty) = &v.ty {
                        self.topo_visit_ty(ty, list, visited);
                    }
                }
            }
        }
        list.push(id);
    }

    fn topo_visit_ty(&self, ty: &Type, list: &mut Vec<TypeId>, visited: &mut HashSet<TypeId>) {
        if let Type::Id(id) = ty {
            self.topo_visit(*id, list, visited);
        }
    }

    pub fn all_bits_valid(&self, ty: &Type) -> bool {
        match ty {
            Type::Unit
            | Type::U8
            | Type::S8
            | Type::U16
            | Type::S16
            | Type::U32
            | Type::S32
            | Type::U64
            | Type::S64
            | Type::Float32
            | Type::Float64 => true,

            Type::Bool | Type::Char | Type::Handle(_) | Type::String => false,

            Type::Id(id) => match &self.types[*id].kind {
                TypeDefKind::List(_) | TypeDefKind::Variant(_) => false,
                TypeDefKind::Type(t) => self.all_bits_valid(t),
                TypeDefKind::Record(r) => r.fields.iter().all(|f| self.all_bits_valid(&f.ty)),

                // FIXME: this could perhaps be `true` for multiples-of-32 but
                // seems better to probably leave this as unconditionally
                // `false` for now, may want to reconsider later?
                TypeDefKind::Flags(_) => false,
            },
        }
    }

    pub fn get_variant(&self, ty: &Type) -> Option<&Variant> {
        if let Type::Id(id) = ty {
            match &self.types[*id].kind {
                TypeDefKind::Variant(v) => Some(v),
                _ => None,
            }
        } else {
            None
        }
    }
}

fn load_fs(root: &Path, name: &str) -> Result<(PathBuf, String)> {
    let wit = root.join(name).with_extension("wit");
    let contents =
        fs::read_to_string(&wit).context(format!("failed to read `{}`", wit.display()))?;
    Ok((wit, contents))
}
