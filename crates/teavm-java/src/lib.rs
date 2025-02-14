use anyhow::Result;
use heck::{ToLowerCamelCase, ToShoutySnakeCase, ToUpperCamelCase};
use std::{
    collections::{HashMap, HashSet},
    fmt::Write,
    iter, mem,
    ops::Deref,
};
use wit_bindgen_core::{
    abi::{self, AbiVariant, Bindgen, Bitcast, Instruction, LiftLower, WasmType},
    uwrite, uwriteln,
    wit_parser::{
        Alignment, ArchitectureSize, Docs, Enum, Flags, FlagsRepr, Function, FunctionKind, Int,
        InterfaceId, Record, Resolve, Result_, SizeAlign, Tuple, Type, TypeDef, TypeDefKind,
        TypeId, TypeOwner, Variant, WorldId, WorldKey,
    },
    Direction, Files, InterfaceGenerator as _, Ns, Source, WorldGenerator,
};

const IMPORTS: &str = "\
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;

import org.teavm.interop.Memory;
import org.teavm.interop.Address;
import org.teavm.interop.Import;
import org.teavm.interop.Export;\
";

#[derive(Default, Debug, Clone)]
#[cfg_attr(feature = "clap", derive(clap::Args))]
pub struct Opts {
    /// Whether or not to generate a stub class for exported functions
    #[cfg_attr(feature = "clap", arg(long))]
    pub generate_stub: bool,
}

impl Opts {
    pub fn build(&self) -> Box<dyn WorldGenerator> {
        Box::new(TeaVmJava {
            opts: self.clone(),
            ..TeaVmJava::default()
        })
    }
}

struct InterfaceFragment {
    src: String,
    stub: String,
}

#[derive(Default)]
pub struct TeaVmJava {
    opts: Opts,
    name: String,
    return_area_size: ArchitectureSize,
    return_area_align: Alignment,
    tuple_counts: HashSet<usize>,
    needs_cleanup: bool,
    needs_result: bool,
    interface_fragments: HashMap<String, Vec<InterfaceFragment>>,
    world_fragments: Vec<InterfaceFragment>,
    sizes: SizeAlign,
    interface_names: HashMap<InterfaceId, String>,
}

impl TeaVmJava {
    fn qualifier(&self) -> String {
        format!("{}.", self.name)
    }

    fn interface<'a>(&'a mut self, resolve: &'a Resolve, name: &'a str) -> InterfaceGenerator<'a> {
        InterfaceGenerator {
            src: String::new(),
            stub: String::new(),
            gen: self,
            resolve,
            name,
        }
    }
}

impl WorldGenerator for TeaVmJava {
    fn preprocess(&mut self, resolve: &Resolve, world: WorldId) {
        self.name = world_name(resolve, world);
        self.sizes.fill(resolve);
    }

    fn import_interface(
        &mut self,
        resolve: &Resolve,
        key: &WorldKey,
        id: InterfaceId,
        _files: &mut Files,
    ) -> Result<()> {
        let name = interface_name(resolve, key, Direction::Import);
        self.interface_names.insert(id, name.clone());
        let mut gen = self.interface(resolve, &name);
        gen.types(id);

        for (_, func) in resolve.interfaces[id].functions.iter() {
            gen.import(&resolve.name_world_key(key), func);
        }

        gen.add_interface_fragment();

        Ok(())
    }

    fn import_funcs(
        &mut self,
        resolve: &Resolve,
        world: WorldId,
        funcs: &[(&str, &Function)],
        _files: &mut Files,
    ) {
        let name = world_name(resolve, world);
        let mut gen = self.interface(resolve, &name);

        for (_, func) in funcs {
            gen.import("$root", func);
        }

        gen.add_world_fragment();
    }

    fn export_interface(
        &mut self,
        resolve: &Resolve,
        key: &WorldKey,
        id: InterfaceId,
        _files: &mut Files,
    ) -> Result<()> {
        let name = interface_name(resolve, key, Direction::Export);
        self.interface_names.insert(id, name.clone());
        let mut gen = self.interface(resolve, &name);
        gen.types(id);

        for (_, func) in resolve.interfaces[id].functions.iter() {
            gen.export(Some(&resolve.name_world_key(key)), func);
        }

        gen.add_interface_fragment();
        Ok(())
    }

    fn export_funcs(
        &mut self,
        resolve: &Resolve,
        world: WorldId,
        funcs: &[(&str, &Function)],
        _files: &mut Files,
    ) -> Result<()> {
        let name = world_name(resolve, world);
        let mut gen = self.interface(resolve, &name);

        for (_, func) in funcs {
            gen.export(None, func);
        }

        gen.add_world_fragment();
        Ok(())
    }

    fn import_types(
        &mut self,
        resolve: &Resolve,
        world: WorldId,
        types: &[(&str, TypeId)],
        _files: &mut Files,
    ) {
        let name = world_name(resolve, world);
        let mut gen = self.interface(resolve, &name);

        for (ty_name, ty) in types {
            gen.define_type(ty_name, *ty);
        }

        gen.add_world_fragment();
    }

    fn finish(&mut self, resolve: &Resolve, id: WorldId, files: &mut Files) -> Result<()> {
        let name = world_name(resolve, id);
        let (package, name) = split_qualified_name(&name);

        let mut src = Source::default();
        let version = env!("CARGO_PKG_VERSION");
        wit_bindgen_core::generated_preamble(&mut src, version);

        uwrite!(
            src,
            "package {package};

             {IMPORTS}
             import org.teavm.interop.CustomSection;

             public final class {name} {{
                private {name}() {{}}
            "
        );

        src.push_str(
            &self
                .world_fragments
                .iter()
                .map(|f| f.src.deref())
                .collect::<Vec<_>>()
                .join("\n"),
        );

        let mut producers = wasm_metadata::Producers::empty();
        producers.add(
            "processed-by",
            env!("CARGO_PKG_NAME"),
            env!("CARGO_PKG_VERSION"),
        );

        let component_type = wit_component::metadata::encode(
            resolve,
            id,
            wit_component::StringEncoding::UTF8,
            Some(&producers),
        )
        .unwrap();

        let component_type = component_type
            .into_iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<Vec<_>>()
            .concat();

        uwriteln!(
            src,
            r#"
            @CustomSection(name = "component-type:{name}")
            private static final String __WIT_BINDGEN_COMPONENT_TYPE = "{component_type}";
            "#
        );

        for &count in &self.tuple_counts {
            let (type_params, instance) = if count == 0 {
                (
                    String::new(),
                    "public static final Tuple0 INSTANCE = new Tuple0();",
                )
            } else {
                (
                    format!(
                        "<{}>",
                        (0..count)
                            .map(|index| format!("T{index}"))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                    "",
                )
            };
            let value_params = (0..count)
                .map(|index| format!("T{index} f{index}"))
                .collect::<Vec<_>>()
                .join(", ");
            let fields = (0..count)
                .map(|index| format!("public final T{index} f{index};"))
                .collect::<Vec<_>>()
                .join("\n");
            let inits = (0..count)
                .map(|index| format!("this.f{index} = f{index};"))
                .collect::<Vec<_>>()
                .join("\n");

            uwrite!(
                src,
                "
                public static final class Tuple{count}{type_params} {{
                    {fields}

                    public Tuple{count}({value_params}) {{
                        {inits}
                    }}

                    {instance}
                }}
                "
            )
        }

        if self.needs_result {
            src.push_str(
                r#"
                public static final class Result<Ok, Err> {
                    public final byte tag;
                    private final Object value;

                    private Result(byte tag, Object value) {
                        this.tag = tag;
                        this.value = value;
                    }

                    public static <Ok, Err> Result<Ok, Err> ok(Ok ok) {
                        return new Result<>(OK, ok);
                    }

                    public static <Ok, Err> Result<Ok, Err> err(Err err) {
                        return new Result<>(ERR, err);
                    }

                    public Ok getOk() {
                        if (this.tag == OK) {
                            return (Ok) this.value;
                        } else {
                            throw new RuntimeException("expected OK, got " + this.tag);
                        }
                    }

                    public Err getErr() {
                        if (this.tag == ERR) {
                            return (Err) this.value;
                        } else {
                            throw new RuntimeException("expected ERR, got " + this.tag);
                        }
                    }

                    public static final byte OK = 0;
                    public static final byte ERR = 1;
                }
                "#,
            )
        }

        if self.needs_cleanup {
            src.push_str(
                "
                public static final class Cleanup {
                    public final int address;
                    public final int size;
                    public final int align;

                    public Cleanup(int address, int size, int align) {
                        this.address = address;
                        this.size = size;
                        this.align = align;
                    }
                }
                ",
            );
        }

        if !self.return_area_size.is_empty() {
            let size = self.return_area_size.size_wasm32();
            let align = self.return_area_align.align_wasm32();

            uwriteln!(
                src,
                "public static final int RETURN_AREA = Memory.malloc({size}, {align}).toInt();",
            );
        }

        src.push_str("}\n");

        let directory = package.replace('.', "/");
        files.push(&format!("{directory}/{name}.java"), indent(&src).as_bytes());

        let generate_stub =
            |package: &str, name, fragments: &[InterfaceFragment], files: &mut Files| {
                let b = fragments
                    .iter()
                    .map(|f| f.stub.deref())
                    .collect::<Vec<_>>()
                    .join("\n");

                let mut body = Source::default();
                wit_bindgen_core::generated_preamble(&mut body, version);
                uwriteln!(
                    &mut body,
                    "package {package};

                 {IMPORTS}

                 public class {name} {{
                     {b}
                 }}
                "
                );

                let directory = package.replace('.', "/");
                files.push(
                    &format!("{directory}/{name}.java"),
                    indent(&body).as_bytes(),
                );
            };

        if self.opts.generate_stub {
            generate_stub(
                &package,
                format!("{name}Impl"),
                &self.world_fragments,
                files,
            );
        }

        for (name, fragments) in &self.interface_fragments {
            let (package, name) = split_qualified_name(name);

            let b = fragments
                .iter()
                .map(|f| f.src.deref())
                .collect::<Vec<_>>()
                .join("\n");

            let mut body = Source::default();
            wit_bindgen_core::generated_preamble(&mut body, version);
            uwriteln!(
                &mut body,
                "package {package};

                 {IMPORTS}

                 public final class {name} {{
                     private {name}() {{}}

                     {b}
                 }}
                "
            );

            let directory = package.replace('.', "/");
            files.push(
                &format!("{directory}/{name}.java"),
                indent(&body).as_bytes(),
            );

            if self.opts.generate_stub {
                generate_stub(&package, format!("{name}Impl"), fragments, files);
            }
        }

        Ok(())
    }
}

struct InterfaceGenerator<'a> {
    src: String,
    stub: String,
    gen: &'a mut TeaVmJava,
    resolve: &'a Resolve,
    name: &'a str,
}

impl InterfaceGenerator<'_> {
    fn qualifier(&self, when: bool, ty: &TypeDef) -> String {
        if let TypeOwner::Interface(id) = &ty.owner {
            if let Some(name) = self.gen.interface_names.get(id) {
                if name != self.name {
                    return format!("{name}.");
                }
            }
        }

        if when {
            format!("{}.", self.name)
        } else {
            String::new()
        }
    }

    fn add_interface_fragment(self) {
        self.gen
            .interface_fragments
            .entry(self.name.to_owned())
            .or_default()
            .push(InterfaceFragment {
                src: self.src,
                stub: self.stub,
            });
    }

    fn add_world_fragment(self) {
        self.gen.world_fragments.push(InterfaceFragment {
            src: self.src,
            stub: self.stub,
        });
    }

    fn import(&mut self, module: &str, func: &Function) {
        if func.kind != FunctionKind::Freestanding {
            todo!("resources");
        }

        let mut bindgen = FunctionBindgen::new(
            self,
            &func.name,
            func.params
                .iter()
                .map(|(name, _)| name.to_java_ident())
                .collect(),
        );

        abi::call(
            bindgen.gen.resolve,
            AbiVariant::GuestImport,
            LiftLower::LowerArgsLiftResults,
            func,
            &mut bindgen,
            false,
        );

        let src = bindgen.src;

        let cleanup_list = if bindgen.needs_cleanup_list {
            self.gen.needs_cleanup = true;

            format!(
                "ArrayList<{}Cleanup> cleanupList = new ArrayList<>();\n",
                self.gen.qualifier()
            )
        } else {
            String::new()
        };

        let name = &func.name;

        let sig = self.resolve.wasm_signature(AbiVariant::GuestImport, func);

        let result_type = match &sig.results[..] {
            [] => "void",
            [result] => wasm_type(*result),
            _ => unreachable!(),
        };

        let camel_name = func.name.to_upper_camel_case();

        let params = sig
            .params
            .iter()
            .enumerate()
            .map(|(i, param)| {
                let ty = wasm_type(*param);
                format!("{ty} p{i}")
            })
            .collect::<Vec<_>>()
            .join(", ");

        let sig = self.sig_string(func, false);

        uwrite!(
            self.src,
            r#"@Import(name = "{name}", module = "{module}")
               private static native {result_type} wasmImport{camel_name}({params});

               {sig} {{
                   {cleanup_list} {src}
               }}
            "#
        );
    }

    fn export(&mut self, interface_name: Option<&str>, func: &Function) {
        let sig = self.resolve.wasm_signature(AbiVariant::GuestExport, func);

        let export_name = func.legacy_core_export_name(interface_name);

        let mut bindgen = FunctionBindgen::new(
            self,
            &func.name,
            (0..sig.params.len()).map(|i| format!("p{i}")).collect(),
        );

        abi::call(
            bindgen.gen.resolve,
            AbiVariant::GuestExport,
            LiftLower::LiftArgsLowerResults,
            func,
            &mut bindgen,
            false,
        );

        assert!(!bindgen.needs_cleanup_list);

        let src = bindgen.src;

        let result_type = match &sig.results[..] {
            [] => "void",
            [result] => wasm_type(*result),
            _ => unreachable!(),
        };

        let camel_name = func.name.to_upper_camel_case();

        let params = sig
            .params
            .iter()
            .enumerate()
            .map(|(i, param)| {
                let ty = wasm_type(*param);
                format!("{ty} p{i}")
            })
            .collect::<Vec<_>>()
            .join(", ");

        uwrite!(
            self.src,
            r#"
            @Export(name = "{export_name}")
            private static {result_type} wasmExport{camel_name}({params}) {{
                {src}
            }}
            "#
        );

        if abi::guest_export_needs_post_return(self.resolve, func) {
            let params = sig
                .results
                .iter()
                .enumerate()
                .map(|(i, param)| {
                    let ty = wasm_type(*param);
                    format!("{ty} p{i}")
                })
                .collect::<Vec<_>>()
                .join(", ");

            let mut bindgen = FunctionBindgen::new(
                self,
                "INVALID",
                (0..sig.results.len()).map(|i| format!("p{i}")).collect(),
            );

            abi::post_return(bindgen.gen.resolve, func, &mut bindgen, false);

            let src = bindgen.src;

            uwrite!(
                self.src,
                r#"
                @Export(name = "cabi_post_{export_name}")
                private static void wasmExport{camel_name}PostReturn({params}) {{
                    {src}
                }}
                "#
            );
        }

        if self.gen.opts.generate_stub {
            let sig = self.sig_string(func, true);

            uwrite!(
                self.stub,
                r#"
                {sig} {{
                    throw new RuntimeException("todo");
                }}
                "#
            );
        }
    }

    fn type_name(&mut self, ty: &Type) -> String {
        self.type_name_with_qualifier(ty, false)
    }

    fn type_name_with_qualifier(&mut self, ty: &Type, qualifier: bool) -> String {
        match ty {
            Type::Bool => "boolean".into(),
            Type::U8 | Type::S8 => "byte".into(),
            Type::U16 | Type::S16 => "short".into(),
            Type::U32 | Type::S32 | Type::Char => "int".into(),
            Type::U64 | Type::S64 => "long".into(),
            Type::F32 => "float".into(),
            Type::F64 => "double".into(),
            Type::String => "String".into(),
            Type::Id(id) => {
                let ty = &self.resolve.types[*id];
                match &ty.kind {
                    TypeDefKind::Type(ty) => self.type_name_with_qualifier(ty, qualifier),
                    TypeDefKind::List(ty) => {
                        if is_primitive(ty) {
                            format!("{}[]", self.type_name(ty))
                        } else {
                            format!("ArrayList<{}>", self.type_name_boxed(ty, qualifier))
                        }
                    }
                    TypeDefKind::Tuple(tuple) => {
                        let count = tuple.types.len();
                        self.gen.tuple_counts.insert(count);

                        let params = if count == 0 {
                            String::new()
                        } else {
                            format!(
                                "<{}>",
                                tuple
                                    .types
                                    .iter()
                                    .map(|ty| self.type_name_boxed(ty, qualifier))
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            )
                        };

                        format!("{}Tuple{count}{params}", self.gen.qualifier())
                    }
                    TypeDefKind::Option(ty) => self.type_name_boxed(ty, qualifier),
                    TypeDefKind::Result(result) => {
                        self.gen.needs_result = true;
                        let mut name = |ty: &Option<Type>| {
                            ty.as_ref()
                                .map(|ty| self.type_name_boxed(ty, qualifier))
                                .unwrap_or_else(|| {
                                    self.gen.tuple_counts.insert(0);

                                    format!("{}Tuple0", self.gen.qualifier())
                                })
                        };
                        let ok = name(&result.ok);
                        let err = name(&result.err);

                        format!("{}Result<{ok}, {err}>", self.gen.qualifier())
                    }
                    _ => {
                        if let Some(name) = &ty.name {
                            format!(
                                "{}{}",
                                self.qualifier(qualifier, ty),
                                name.to_upper_camel_case()
                            )
                        } else {
                            unreachable!()
                        }
                    }
                }
            }
        }
    }

    fn type_name_boxed(&mut self, ty: &Type, qualifier: bool) -> String {
        match ty {
            Type::Bool => "Boolean".into(),
            Type::U8 | Type::S8 => "Byte".into(),
            Type::U16 | Type::S16 => "Short".into(),
            Type::U32 | Type::S32 | Type::Char => "Integer".into(),
            Type::U64 | Type::S64 => "Long".into(),
            Type::F32 => "Float".into(),
            Type::F64 => "Double".into(),
            Type::Id(id) => {
                let def = &self.resolve.types[*id];
                match &def.kind {
                    TypeDefKind::Type(ty) => self.type_name_boxed(ty, qualifier),
                    _ => self.type_name_with_qualifier(ty, qualifier),
                }
            }
            _ => self.type_name_with_qualifier(ty, qualifier),
        }
    }

    fn print_docs(&mut self, docs: &Docs) {
        if let Some(docs) = &docs.contents {
            let lines = docs
                .trim()
                .lines()
                .map(|line| format!("* {line}"))
                .collect::<Vec<_>>()
                .join("\n");

            uwrite!(
                self.src,
                "
                /**
                 {lines}
                 */
                "
            )
        }
    }

    fn non_empty_type<'a>(&self, ty: Option<&'a Type>) -> Option<&'a Type> {
        if let Some(ty) = ty {
            let id = match ty {
                Type::Id(id) => *id,
                _ => return Some(ty),
            };
            match &self.resolve.types[id].kind {
                TypeDefKind::Type(t) => self.non_empty_type(Some(t)).map(|_| ty),
                TypeDefKind::Record(r) => (!r.fields.is_empty()).then_some(ty),
                TypeDefKind::Tuple(t) => (!t.types.is_empty()).then_some(ty),
                _ => Some(ty),
            }
        } else {
            None
        }
    }

    fn sig_string(&mut self, func: &Function, qualifier: bool) -> String {
        let name = func.name.to_java_ident();

        let result_type = match func.results.len() {
            0 => "void".into(),
            1 => {
                self.type_name_with_qualifier(func.results.iter_types().next().unwrap(), qualifier)
            }
            count => {
                self.gen.tuple_counts.insert(count);
                format!(
                    "{}Tuple{count}<{}>",
                    self.gen.qualifier(),
                    func.results
                        .iter_types()
                        .map(|ty| self.type_name_boxed(ty, qualifier))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        };

        let params = func
            .params
            .iter()
            .map(|(name, ty)| {
                let ty = self.type_name_with_qualifier(ty, qualifier);
                let name = name.to_java_ident();
                format!("{ty} {name}")
            })
            .collect::<Vec<_>>()
            .join(", ");

        format!("public static {result_type} {name}({params})")
    }
}

impl<'a> wit_bindgen_core::InterfaceGenerator<'a> for InterfaceGenerator<'a> {
    fn resolve(&self) -> &'a Resolve {
        self.resolve
    }

    fn type_record(&mut self, _id: TypeId, name: &str, record: &Record, docs: &Docs) {
        self.print_docs(docs);

        let name = name.to_upper_camel_case();

        let parameters = record
            .fields
            .iter()
            .map(|field| {
                format!(
                    "{} {}",
                    self.type_name(&field.ty),
                    field.name.to_java_ident()
                )
            })
            .collect::<Vec<_>>()
            .join(", ");

        let assignments = record
            .fields
            .iter()
            .map(|field| {
                let name = field.name.to_java_ident();
                format!("this.{name} = {name};")
            })
            .collect::<Vec<_>>()
            .join("\n");

        let fields = if record.fields.is_empty() {
            format!("public static final {name} INSTANCE = new {name}();")
        } else {
            record
                .fields
                .iter()
                .map(|field| {
                    format!(
                        "public final {} {};",
                        self.type_name(&field.ty),
                        field.name.to_java_ident()
                    )
                })
                .collect::<Vec<_>>()
                .join("\n")
        };

        uwrite!(
            self.src,
            "
            public static final class {name} {{
                {fields}

                public {name}({parameters}) {{
                    {assignments}
                }}
            }}
            "
        );
    }

    fn type_resource(&mut self, id: TypeId, name: &str, docs: &Docs) {
        _ = (id, name, docs);
        todo!()
    }

    fn type_flags(&mut self, _id: TypeId, name: &str, flags: &Flags, docs: &Docs) {
        self.print_docs(docs);

        let name = name.to_upper_camel_case();

        let ty = match flags.repr() {
            FlagsRepr::U8 => "byte",
            FlagsRepr::U16 => "short",
            FlagsRepr::U32(1) => "int",
            FlagsRepr::U32(2) => "long",
            repr => todo!("flags {repr:?}"),
        };

        let flags = flags
            .flags
            .iter()
            .enumerate()
            .map(|(i, flag)| {
                let flag_name = flag.name.to_shouty_snake_case();
                let suffix = if matches!(flags.repr(), FlagsRepr::U32(2)) {
                    "L"
                } else {
                    ""
                };
                format!(
                    "public static final {name} {flag_name} = new {name}(({ty}) (1{suffix} << {i}));"
                )
            })
            .collect::<Vec<_>>()
            .join("\n");

        uwrite!(
            self.src,
            "
            public static final class {name} {{
                public final {ty} value;

                public {name}({ty} value) {{
                    this.value = value;
                }}

                {flags}
            }}
            "
        );
    }

    fn type_tuple(&mut self, id: TypeId, _name: &str, _tuple: &Tuple, _docs: &Docs) {
        self.type_name(&Type::Id(id));
    }

    fn type_variant(&mut self, _id: TypeId, name: &str, variant: &Variant, docs: &Docs) {
        self.print_docs(docs);

        let name = name.to_upper_camel_case();
        let tag_type = int_type(variant.tag());

        let constructors = variant
            .cases
            .iter()
            .map(|case| {
                let case_name = case.name.to_java_ident();
                let tag = case.name.to_shouty_snake_case();
                let (parameter, argument) = if let Some(ty) = self.non_empty_type(case.ty.as_ref())
                {
                    (
                        format!("{} {case_name}", self.type_name(ty)),
                        case_name.deref(),
                    )
                } else {
                    (String::new(), "null")
                };

                format!(
                    "public static {name} {case_name}({parameter}) {{
                         return new {name}({tag}, {argument});
                     }}
                    "
                )
            })
            .collect::<Vec<_>>()
            .join("\n");

        let accessors = variant
            .cases
            .iter()
            .filter_map(|case| {
                self.non_empty_type(case.ty.as_ref()).map(|ty| {
                    let case_name = case.name.to_upper_camel_case();
                    let tag = case.name.to_shouty_snake_case();
                    let ty = self.type_name(ty);
                    format!(
                        r#"public {ty} get{case_name}() {{
                               if (this.tag == {tag}) {{
                                   return ({ty}) this.value;
                               }} else {{
                                   throw new RuntimeException("expected {tag}, got " + this.tag);
                               }}
                           }}
                        "#
                    )
                })
            })
            .collect::<Vec<_>>()
            .join("\n");

        let tags = variant
            .cases
            .iter()
            .enumerate()
            .map(|(i, case)| {
                let tag = case.name.to_shouty_snake_case();
                format!("public static final {tag_type} {tag} = {i};")
            })
            .collect::<Vec<_>>()
            .join("\n");

        uwrite!(
            self.src,
            "
            public static final class {name} {{
                public final {tag_type} tag;
                private final Object value;

                private {name}({tag_type} tag, Object value) {{
                    this.tag = tag;
                    this.value = value;
                }}

                {constructors}
                {accessors}
                {tags}
            }}
            "
        );
    }

    fn type_option(&mut self, id: TypeId, _name: &str, _payload: &Type, _docs: &Docs) {
        self.type_name(&Type::Id(id));
    }

    fn type_result(&mut self, id: TypeId, _name: &str, _result: &Result_, _docs: &Docs) {
        self.type_name(&Type::Id(id));
    }

    fn type_enum(&mut self, _id: TypeId, name: &str, enum_: &Enum, docs: &Docs) {
        self.print_docs(docs);

        let name = name.to_upper_camel_case();

        let cases = enum_
            .cases
            .iter()
            .map(|case| case.name.to_shouty_snake_case())
            .collect::<Vec<_>>()
            .join(", ");

        uwrite!(
            self.src,
            "
            public static enum {name} {{
                {cases}
            }}
            "
        );
    }

    fn type_alias(&mut self, id: TypeId, _name: &str, _ty: &Type, _docs: &Docs) {
        self.type_name(&Type::Id(id));
    }

    fn type_list(&mut self, id: TypeId, _name: &str, _ty: &Type, _docs: &Docs) {
        self.type_name(&Type::Id(id));
    }

    fn type_future(&mut self, id: TypeId, name: &str, ty: &Option<Type>, docs: &Docs) {
        _ = (id, name, ty, docs);
        todo!()
    }

    fn type_stream(&mut self, id: TypeId, name: &str, ty: &Option<Type>, docs: &Docs) {
        _ = (id, name, ty, docs);
        todo!()
    }

    fn type_error_context(&mut self, id: TypeId, name: &str, docs: &Docs) {
        _ = (id, name, docs);
        todo!()
    }

    fn type_builtin(&mut self, _id: TypeId, _name: &str, _ty: &Type, _docs: &Docs) {
        unimplemented!();
    }
}

struct Block {
    body: String,
    results: Vec<String>,
    element: String,
    base: String,
}

struct Cleanup {
    address: String,
    size: String,
    align: usize,
}

struct BlockStorage {
    body: String,
    element: String,
    base: String,
    cleanup: Vec<Cleanup>,
}

struct FunctionBindgen<'a, 'b> {
    gen: &'b mut InterfaceGenerator<'a>,
    func_name: &'b str,
    params: Box<[String]>,
    src: String,
    locals: Ns,
    block_storage: Vec<BlockStorage>,
    blocks: Vec<Block>,
    payloads: Vec<String>,
    cleanup: Vec<Cleanup>,
    needs_cleanup_list: bool,
}

impl<'a, 'b> FunctionBindgen<'a, 'b> {
    fn new(
        gen: &'b mut InterfaceGenerator<'a>,
        func_name: &'b str,
        params: Box<[String]>,
    ) -> FunctionBindgen<'a, 'b> {
        Self {
            gen,
            func_name,
            params,
            src: String::new(),
            locals: Ns::default(),
            block_storage: Vec::new(),
            blocks: Vec::new(),
            payloads: Vec::new(),
            cleanup: Vec::new(),
            needs_cleanup_list: false,
        }
    }

    fn lower_variant(
        &mut self,
        cases: &[(&str, Option<Type>)],
        lowered_types: &[WasmType],
        op: &str,
        results: &mut Vec<String>,
    ) {
        let blocks = self
            .blocks
            .drain(self.blocks.len() - cases.len()..)
            .collect::<Vec<_>>();

        let payloads = self
            .payloads
            .drain(self.payloads.len() - cases.len()..)
            .collect::<Vec<_>>();

        let lowered = lowered_types
            .iter()
            .map(|_| self.locals.tmp("lowered"))
            .collect::<Vec<_>>();

        results.extend(lowered.iter().cloned());

        let declarations = lowered
            .iter()
            .zip(lowered_types)
            .map(|(lowered, ty)| format!("{} {lowered};", wasm_type(*ty)))
            .collect::<Vec<_>>()
            .join("\n");

        let cases = cases
            .iter()
            .zip(blocks)
            .zip(payloads)
            .enumerate()
            .map(
                |(i, (((name, ty), Block { body, results, .. }), payload))| {
                    let payload = if let Some(ty) = self.gen.non_empty_type(ty.as_ref()) {
                        let ty = self.gen.type_name(ty);
                        let name = name.to_upper_camel_case();

                        format!("{ty} {payload} = ({op}).get{name}();")
                    } else {
                        String::new()
                    };

                    let assignments = lowered
                        .iter()
                        .zip(&results)
                        .map(|(lowered, result)| format!("{lowered} = {result};\n"))
                        .collect::<Vec<_>>()
                        .concat();

                    format!(
                        "case {i}: {{
                         {payload}
                         {body}
                         {assignments}
                         break;
                     }}"
                    )
                },
            )
            .collect::<Vec<_>>()
            .join("\n");

        uwrite!(
            self.src,
            r#"
            {declarations}

            switch (({op}).tag) {{
                {cases}

                default: throw new AssertionError("invalid discriminant: " + ({op}).tag);
            }}
            "#
        );
    }

    fn lift_variant(
        &mut self,
        ty: &Type,
        cases: &[(&str, Option<Type>)],
        op: &str,
        results: &mut Vec<String>,
    ) {
        let blocks = self
            .blocks
            .drain(self.blocks.len() - cases.len()..)
            .collect::<Vec<_>>();

        let ty = self.gen.type_name(ty);
        let generics_position = ty.find('<');
        let lifted = self.locals.tmp("lifted");

        let cases = cases
            .iter()
            .zip(blocks)
            .enumerate()
            .map(|(i, ((case_name, case_ty), Block { body, results, .. }))| {
                let payload = if self.gen.non_empty_type(case_ty.as_ref()).is_some() {
                    results.into_iter().next().unwrap()
                } else if generics_position.is_some() {
                    if let Some(ty) = case_ty.as_ref() {
                        format!("{}.INSTANCE", self.gen.type_name(ty))
                    } else {
                        format!("{}Tuple0.INSTANCE", self.gen.gen.qualifier())
                    }
                } else {
                    String::new()
                };

                let method = case_name.to_java_ident();

                let call = if let Some(position) = generics_position {
                    let (ty, generics) = ty.split_at(position);
                    format!("{ty}.{generics}{method}")
                } else {
                    format!("{ty}.{method}")
                };

                format!(
                    "case {i}: {{
                         {body}
                         {lifted} = {call}({payload});
                         break;
                     }}"
                )
            })
            .collect::<Vec<_>>()
            .join("\n");

        uwrite!(
            self.src,
            r#"
            {ty} {lifted};

            switch ({op}) {{
                {cases}

                default: throw new AssertionError("invalid discriminant: " + ({op}));
            }}
            "#
        );

        results.push(lifted);
    }
}

impl Bindgen for FunctionBindgen<'_, '_> {
    type Operand = String;

    fn emit(
        &mut self,
        _resolve: &Resolve,
        inst: &Instruction<'_>,
        operands: &mut Vec<String>,
        results: &mut Vec<String>,
    ) {
        match inst {
            Instruction::GetArg { nth } => results.push(self.params[*nth].clone()),
            Instruction::I32Const { val } => results.push(val.to_string()),
            Instruction::ConstZero { tys } => results.extend(tys.iter().map(|ty| {
                match ty {
                    WasmType::I32 => "0",
                    WasmType::I64 => "0L",
                    WasmType::F32 => "0.0F",
                    WasmType::F64 => "0.0D",
                    WasmType::Pointer => "0",
                    WasmType::PointerOrI64 => "0L",
                    WasmType::Length => "0",
                }
                .to_owned()
            })),

            // TODO: checked
            Instruction::U8FromI32 => results.push(format!("(byte) ({})", operands[0])),
            Instruction::S8FromI32 => results.push(format!("(byte) ({})", operands[0])),
            Instruction::U16FromI32 => results.push(format!("(short) ({})", operands[0])),
            Instruction::S16FromI32 => results.push(format!("(short) ({})", operands[0])),

            Instruction::I32FromU8 => results.push(format!("((int) ({})) & 0xFF", operands[0])),
            Instruction::I32FromU16 => results.push(format!("((int) ({})) & 0xFFFF", operands[0])),

            Instruction::I32FromS8 | Instruction::I32FromS16 => {
                results.push(format!("(int) ({})", operands[0]))
            }

            Instruction::CharFromI32
            | Instruction::I32FromChar
            | Instruction::U32FromI32
            | Instruction::S32FromI32
            | Instruction::S64FromI64
            | Instruction::U64FromI64
            | Instruction::I32FromU32
            | Instruction::I32FromS32
            | Instruction::I64FromS64
            | Instruction::I64FromU64
            | Instruction::CoreF32FromF32
            | Instruction::CoreF64FromF64
            | Instruction::F32FromCoreF32
            | Instruction::F64FromCoreF64 => results.push(operands[0].clone()),

            Instruction::Bitcasts { casts } => results.extend(
                casts
                    .iter()
                    .zip(operands)
                    .map(|(cast, op)| perform_cast(op, cast)),
            ),

            Instruction::I32FromBool => {
                results.push(format!("({} ? 1 : 0)", operands[0]));
            }
            Instruction::BoolFromI32 => results.push(format!("({} != 0)", operands[0])),

            // TODO: checked
            Instruction::FlagsLower { flags, .. } => match flags_repr(flags) {
                Int::U8 | Int::U16 | Int::U32 => {
                    results.push(format!("({}).value", operands[0]));
                }
                Int::U64 => {
                    let op = &operands[0];
                    results.push(format!("(int) (({op}).value & 0xffffffffL)"));
                    results.push(format!("(int) ((({op}).value >>> 32) & 0xffffffffL)"));
                }
            },

            Instruction::FlagsLift { flags, ty, .. } => match flags_repr(flags) {
                Int::U8 | Int::U16 | Int::U32 => {
                    results.push(format!(
                        "new {}(({}) {})",
                        self.gen.type_name(&Type::Id(*ty)),
                        int_type(flags_repr(flags)),
                        operands[0]
                    ));
                }
                Int::U64 => {
                    results.push(format!(
                        "new {}(((long) ({})) | (((long) ({})) << 32))",
                        self.gen.type_name(&Type::Id(*ty)),
                        operands[0],
                        operands[1]
                    ));
                }
            },

            Instruction::HandleLower { .. } | Instruction::HandleLift { .. } => todo!(),

            Instruction::RecordLower { record, .. } => {
                let op = &operands[0];
                for field in record.fields.iter() {
                    results.push(format!("({op}).{}", field.name.to_java_ident()));
                }
            }
            Instruction::RecordLift { ty, .. } | Instruction::TupleLift { ty, .. } => {
                let ops = operands
                    .iter()
                    .map(|op| op.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");

                results.push(format!("new {}({ops})", self.gen.type_name(&Type::Id(*ty))));
            }

            Instruction::TupleLower { tuple, .. } => {
                let op = &operands[0];
                for i in 0..tuple.types.len() {
                    results.push(format!("({op}).f{i}"));
                }
            }

            Instruction::VariantPayloadName => {
                let payload = self.locals.tmp("payload");
                results.push(payload.clone());
                self.payloads.push(payload);
            }

            Instruction::VariantLower {
                variant,
                results: lowered_types,
                ..
            } => self.lower_variant(
                &variant
                    .cases
                    .iter()
                    .map(|case| (case.name.deref(), case.ty))
                    .collect::<Vec<_>>(),
                lowered_types,
                &operands[0],
                results,
            ),

            Instruction::VariantLift { variant, ty, .. } => self.lift_variant(
                &Type::Id(*ty),
                &variant
                    .cases
                    .iter()
                    .map(|case| (case.name.deref(), case.ty))
                    .collect::<Vec<_>>(),
                &operands[0],
                results,
            ),

            Instruction::OptionLower {
                results: lowered_types,
                payload,
                ..
            } => {
                let some = self.blocks.pop().unwrap();
                let none = self.blocks.pop().unwrap();
                let some_payload = self.payloads.pop().unwrap();
                let none_payload = self.payloads.pop().unwrap();

                let lowered = lowered_types
                    .iter()
                    .map(|_| self.locals.tmp("lowered"))
                    .collect::<Vec<_>>();

                results.extend(lowered.iter().cloned());

                let declarations = lowered
                    .iter()
                    .zip(lowered_types.iter())
                    .map(|(lowered, ty)| format!("{} {lowered};", wasm_type(*ty)))
                    .collect::<Vec<_>>()
                    .join("\n");

                let op = &operands[0];

                let mut block = |ty: Option<&Type>, Block { body, results, .. }, payload| {
                    let payload = if let Some(ty) = self.gen.non_empty_type(ty) {
                        let ty = self.gen.type_name(ty);

                        format!("{ty} {payload} = ({ty}) ({op});")
                    } else {
                        String::new()
                    };

                    let assignments = lowered
                        .iter()
                        .zip(&results)
                        .map(|(lowered, result)| format!("{lowered} = {result};\n"))
                        .collect::<Vec<_>>()
                        .concat();

                    format!(
                        "{payload}
                         {body}
                         {assignments}"
                    )
                };

                let none = block(None, none, none_payload);
                let some = block(Some(payload), some, some_payload);

                uwrite!(
                    self.src,
                    r#"
                    {declarations}

                    if (({op}) == null) {{
                        {none}
                    }} else {{
                        {some}
                    }}
                    "#
                );
            }

            Instruction::OptionLift { payload, ty } => {
                let some = self.blocks.pop().unwrap();
                let _none = self.blocks.pop().unwrap();

                let ty = self.gen.type_name(&Type::Id(*ty));
                let lifted = self.locals.tmp("lifted");
                let op = &operands[0];

                let payload = if self.gen.non_empty_type(Some(*payload)).is_some() {
                    some.results.into_iter().next().unwrap()
                } else {
                    "null".into()
                };

                let some = some.body;

                uwrite!(
                    self.src,
                    r#"
                    {ty} {lifted};

                    switch ({op}) {{
                        case 0: {{
                            {lifted} = null;
                            break;
                        }}

                        case 1: {{
                            {some}
                            {lifted} = {payload};
                            break;
                        }}

                        default: throw new AssertionError("invalid discriminant: " + ({op}));
                    }}
                    "#
                );

                results.push(lifted);
            }

            Instruction::ResultLower {
                results: lowered_types,
                result,
                ..
            } => self.lower_variant(
                &[("ok", result.ok), ("err", result.err)],
                lowered_types,
                &operands[0],
                results,
            ),

            Instruction::ResultLift { result, ty } => self.lift_variant(
                &Type::Id(*ty),
                &[("ok", result.ok), ("err", result.err)],
                &operands[0],
                results,
            ),

            Instruction::EnumLower { .. } => results.push(format!("{}.ordinal()", operands[0])),

            Instruction::EnumLift { ty, .. } => results.push(format!(
                "{}.values()[{}]",
                self.gen.type_name(&Type::Id(*ty)),
                operands[0]
            )),

            Instruction::ListCanonLower { element, realloc } => {
                let op = &operands[0];
                let (size, ty) = list_element_info(element);

                // Note that we can only reliably use `Address.ofData` for elements with alignment <= 4 because as
                // of this writing TeaVM does not guarantee 64 bit items are aligned on 8 byte boundaries.
                if realloc.is_none() && size <= 4 {
                    results.push(format!("org.teavm.interop.Address.ofData({op}).toInt()"));
                } else {
                    let address = self.locals.tmp("address");
                    let ty = ty.to_upper_camel_case();

                    uwrite!(
                        self.src,
                        "
                        org.teavm.interop.Address {address} = Memory.malloc({size} * ({op}).length, {size});
                        Memory.put{ty}s({address}, {op}, 0, ({op}).length);
                        "
                    );

                    if realloc.is_none() {
                        self.cleanup.push(Cleanup {
                            address: format!("{address}.toInt()"),
                            size: format!("{size} * ({op}).length"),
                            align: size,
                        });
                    }

                    results.push(format!("{address}.toInt()"));
                }
                results.push(format!("({op}).length"));
            }

            Instruction::ListCanonLift { element, .. } => {
                let (_, ty) = list_element_info(element);
                let ty_upper = ty.to_upper_camel_case();
                let array = self.locals.tmp("array");
                let address = &operands[0];
                let length = &operands[1];

                uwrite!(
                    self.src,
                    "
                    {ty}[] {array} = new {ty}[{length}];
                    Memory.get{ty_upper}s(org.teavm.interop.Address.fromInt({address}), {array}, 0, ({array}).length);
                    "
                );

                results.push(array);
            }

            Instruction::StringLower { realloc } => {
                let op = &operands[0];
                let bytes = self.locals.tmp("bytes");
                uwriteln!(
                    self.src,
                    "byte[] {bytes} = ({op}).getBytes(StandardCharsets.UTF_8);"
                );

                if realloc.is_none() {
                    results.push(format!("org.teavm.interop.Address.ofData({bytes}).toInt()"));
                } else {
                    let address = self.locals.tmp("address");

                    uwrite!(
                        self.src,
                        "
                        org.teavm.interop.Address {address} = Memory.malloc({bytes}.length, 1);
                        Memory.putBytes({address}, {bytes}, 0, {bytes}.length);
                        "
                    );

                    results.push(format!("{address}.toInt()"));
                }
                results.push(format!("{bytes}.length"));
            }

            Instruction::StringLift { .. } => {
                let bytes = self.locals.tmp("bytes");
                let address = &operands[0];
                let length = &operands[1];

                uwrite!(
                    self.src,
                    "
                    byte[] {bytes} = new byte[{length}];
                    Memory.getBytes(org.teavm.interop.Address.fromInt({address}), {bytes}, 0, {length});
                    "
                );

                results.push(format!("new String({bytes}, StandardCharsets.UTF_8)"));
            }

            Instruction::ListLower { element, realloc } => {
                let Block {
                    body,
                    results: block_results,
                    element: block_element,
                    base,
                } = self.blocks.pop().unwrap();
                assert!(block_results.is_empty());

                let op = &operands[0];
                let size = self.gen.gen.sizes.size(element);
                let align = self.gen.gen.sizes.align(element);
                let address = self.locals.tmp("address");
                let ty = self.gen.type_name(element);
                let index = self.locals.tmp("index");

                uwrite!(
                    self.src,
                    "
                    int {address} = Memory.malloc(({op}).size() * {size}, {align}).toInt();
                    for (int {index} = 0; {index} < ({op}).size(); ++{index}) {{
                        {ty} {block_element} = ({op}).get({index});
                        int {base} = {address} + ({index} * {size});
                        {body}
                    }}
                    ",
                    align = align.align_wasm32(),
                    size = size.size_wasm32()
                );

                if realloc.is_none() {
                    self.cleanup.push(Cleanup {
                        address: address.clone(),
                        size: format!("({op}).size() * {size}", size = size.size_wasm32()),
                        align: align.align_wasm32(),
                    });
                }

                results.push(address);
                results.push(format!("({op}).size()"));
            }

            Instruction::ListLift { element, .. } => {
                let Block {
                    body,
                    results: block_results,
                    base,
                    ..
                } = self.blocks.pop().unwrap();
                let address = &operands[0];
                let length = &operands[1];
                let array = self.locals.tmp("array");
                let ty = self.gen.type_name(element);
                let size = self.gen.gen.sizes.size(element).size_wasm32();
                let align = self.gen.gen.sizes.align(element).align_wasm32();
                let index = self.locals.tmp("index");

                let result = match &block_results[..] {
                    [result] => result,
                    _ => todo!("result count == {}", results.len()),
                };

                uwrite!(
                    self.src,
                    "
                    ArrayList<{ty}> {array} = new ArrayList<>({length});
                    for (int {index} = 0; {index} < ({length}); ++{index}) {{
                        int {base} = ({address}) + ({index} * {size});
                        {body}
                        {array}.add({result});
                    }}
                    Memory.free(org.teavm.interop.Address.fromInt({address}), ({length}) * {size}, {align});
                    "
                );

                results.push(array);
            }

            Instruction::IterElem { .. } => {
                results.push(self.block_storage.last().unwrap().element.clone())
            }

            Instruction::IterBasePointer => {
                results.push(self.block_storage.last().unwrap().base.clone())
            }

            Instruction::CallWasm { sig, .. } => {
                let assignment = match &sig.results[..] {
                    [result] => {
                        let ty = wasm_type(*result);
                        let result = self.locals.tmp("result");
                        let assignment = format!("{ty} {result} = ");
                        results.push(result);
                        assignment
                    }

                    [] => String::new(),

                    _ => unreachable!(),
                };

                let func_name = self.func_name.to_upper_camel_case();

                let operands = operands.join(", ");

                uwriteln!(self.src, "{assignment} wasmImport{func_name}({operands});");
            }

            Instruction::CallInterface { func, .. } => {
                let (assignment, destructure) = match func.results.len() {
                    0 => (String::new(), String::new()),
                    1 => {
                        let ty = self
                            .gen
                            .type_name(func.results.iter_types().next().unwrap());
                        let result = self.locals.tmp("result");
                        let assignment = format!("{ty} {result} = ");
                        results.push(result);
                        (assignment, String::new())
                    }
                    count => {
                        self.gen.gen.tuple_counts.insert(count);
                        let ty = format!(
                            "{}Tuple{count}<{}>",
                            self.gen.gen.qualifier(),
                            func.results
                                .iter_types()
                                .map(|ty| self.gen.type_name_boxed(ty, false))
                                .collect::<Vec<_>>()
                                .join(", ")
                        );

                        let result = self.locals.tmp("result");
                        let assignment = format!("{ty} {result} = ");

                        let destructure = func
                            .results
                            .iter_types()
                            .enumerate()
                            .map(|(index, ty)| {
                                let ty = self.gen.type_name(ty);
                                let my_result = self.locals.tmp("result");
                                let assignment = format!("{ty} {my_result} = {result}.f{index};");
                                results.push(my_result);
                                assignment
                            })
                            .collect::<Vec<_>>()
                            .join("\n");

                        (assignment, destructure)
                    }
                };

                let module = self.gen.name;
                let name = func.name.to_java_ident();

                let args = operands.join(", ");

                uwrite!(
                    self.src,
                    "
                    {assignment}{module}Impl.{name}({args});
                    {destructure}
                    "
                );
            }

            Instruction::Return { amt, .. } => {
                for Cleanup {
                    address,
                    size,
                    align,
                } in &self.cleanup
                {
                    uwriteln!(
                        self.src,
                        "Memory.free(org.teavm.interop.Address.fromInt({address}), {size}, {align});"
                    );
                }

                if self.needs_cleanup_list {
                    uwrite!(
                        self.src,
                        "
                        for ({}Cleanup cleanup : cleanupList) {{
                            Memory.free(org.teavm.interop.Address.fromInt(cleanup.address), cleanup.size, cleanup.align);
                        }}
                        ",
                        self.gen.gen.qualifier()
                    );
                }

                match *amt {
                    0 => (),
                    1 => uwriteln!(self.src, "return {};", operands[0]),
                    count => {
                        let results = operands.join(", ");
                        uwriteln!(
                            self.src,
                            "return new {}Tuple{count}<>({results});",
                            self.gen.gen.qualifier()
                        )
                    }
                }
            }

            Instruction::I32Load { offset }
            | Instruction::PointerLoad { offset }
            | Instruction::LengthLoad { offset } => results.push(format!(
                "org.teavm.interop.Address.fromInt(({}) + {offset}).getInt()",
                operands[0],
                offset = offset.size_wasm32()
            )),

            Instruction::I32Load8U { offset } => results.push(format!(
                "(((int) org.teavm.interop.Address.fromInt(({}) + {offset}).getByte()) & 0xFF)",
                operands[0],
                offset = offset.size_wasm32()
            )),

            Instruction::I32Load8S { offset } => results.push(format!(
                "((int) org.teavm.interop.Address.fromInt(({}) + {offset}).getByte())",
                operands[0],
                offset = offset.size_wasm32()
            )),

            Instruction::I32Load16U { offset } => results.push(format!(
                "(((int) org.teavm.interop.Address.fromInt(({}) + {offset}).getShort()) & 0xFFFF)",
                operands[0],
                offset = offset.size_wasm32()
            )),

            Instruction::I32Load16S { offset } => results.push(format!(
                "((int) org.teavm.interop.Address.fromInt(({}) + {offset}).getShort())",
                operands[0],
                offset = offset.size_wasm32()
            )),

            Instruction::I64Load { offset } => results.push(format!(
                "org.teavm.interop.Address.fromInt(({}) + {offset}).getLong()",
                operands[0],
                offset = offset.size_wasm32()
            )),

            Instruction::F32Load { offset } => results.push(format!(
                "org.teavm.interop.Address.fromInt(({}) + {offset}).getFloat()",
                operands[0],
                offset = offset.size_wasm32()
            )),

            Instruction::F64Load { offset } => results.push(format!(
                "org.teavm.interop.Address.fromInt(({}) + {offset}).getDouble()",
                operands[0],
                offset = offset.size_wasm32()
            )),

            Instruction::I32Store { offset }
            | Instruction::PointerStore { offset }
            | Instruction::LengthStore { offset } => uwriteln!(
                self.src,
                "org.teavm.interop.Address.fromInt(({}) + {offset}).putInt({});",
                operands[1],
                operands[0],
                offset = offset.size_wasm32()
            ),

            Instruction::I32Store8 { offset } => uwriteln!(
                self.src,
                "org.teavm.interop.Address.fromInt(({}) + {offset}).putByte((byte) ({}));",
                operands[1],
                operands[0],
                offset = offset.size_wasm32()
            ),

            Instruction::I32Store16 { offset } => uwriteln!(
                self.src,
                "org.teavm.interop.Address.fromInt(({}) + {offset}).putShort((short) ({}));",
                operands[1],
                operands[0],
                offset = offset.size_wasm32()
            ),

            Instruction::I64Store { offset } => uwriteln!(
                self.src,
                "org.teavm.interop.Address.fromInt(({}) + {offset}).putLong({});",
                operands[1],
                operands[0],
                offset = offset.size_wasm32()
            ),

            Instruction::F32Store { offset } => uwriteln!(
                self.src,
                "org.teavm.interop.Address.fromInt(({}) + {offset}).putFloat({});",
                operands[1],
                operands[0],
                offset = offset.size_wasm32()
            ),

            Instruction::F64Store { offset } => uwriteln!(
                self.src,
                "org.teavm.interop.Address.fromInt(({}) + {offset}).putDouble({});",
                operands[1],
                operands[0],
                offset = offset.size_wasm32()
            ),

            Instruction::Malloc { .. } => unimplemented!(),

            Instruction::GuestDeallocate { size, align } => {
                uwriteln!(
                    self.src,
                    "Memory.free(org.teavm.interop.Address.fromInt({}), {size}, {align});",
                    operands[0],
                    size = size.size_wasm32(),
                    align = align.align_wasm32()
                )
            }

            Instruction::GuestDeallocateString => uwriteln!(
                self.src,
                "Memory.free(org.teavm.interop.Address.fromInt({}), {}, 1);",
                operands[0],
                operands[1]
            ),

            Instruction::GuestDeallocateVariant { blocks } => {
                let cases = self
                    .blocks
                    .drain(self.blocks.len() - blocks..)
                    .enumerate()
                    .map(|(i, Block { body, results, .. })| {
                        assert!(results.is_empty());

                        format!(
                            "case {i}: {{
                                 {body}
                                 break;
                             }}"
                        )
                    })
                    .collect::<Vec<_>>()
                    .join("\n");

                let op = &operands[0];

                uwrite!(
                    self.src,
                    "
                    switch ({op}) {{
                        {cases}
                    }}
                    "
                );
            }

            Instruction::GuestDeallocateList { element } => {
                let Block {
                    body,
                    results,
                    base,
                    ..
                } = self.blocks.pop().unwrap();
                assert!(results.is_empty());

                let address = &operands[0];
                let length = &operands[1];

                let size = self.gen.gen.sizes.size(element).size_wasm32();
                let align = self.gen.gen.sizes.align(element).align_wasm32();

                if !body.trim().is_empty() {
                    let index = self.locals.tmp("index");

                    uwrite!(
                        self.src,
                        "
                        for (int {index} = 0; {index} < ({length}); ++{index}) {{
                            int {base} = ({address}) + ({index} * {size});
                            {body}
                        }}
                        "
                    );
                }

                uwriteln!(
                    self.src,
                    "Memory.free(org.teavm.interop.Address.fromInt({address}), ({length}) * {size}, {align});"
                );
            }

            Instruction::Flush { amt } => {
                results.extend(operands.iter().take(*amt).map(|v| v.clone()));
            }

            Instruction::AsyncMalloc { .. }
            | Instruction::AsyncPostCallInterface { .. }
            | Instruction::AsyncCallReturn { .. }
            | Instruction::FutureLower { .. }
            | Instruction::FutureLift { .. }
            | Instruction::StreamLower { .. }
            | Instruction::StreamLift { .. }
            | Instruction::ErrorContextLower { .. }
            | Instruction::ErrorContextLift { .. }
            | Instruction::AsyncCallWasm { .. } => todo!(),
        }
    }

    fn return_pointer(&mut self, size: ArchitectureSize, align: Alignment) -> String {
        self.gen.gen.return_area_size = self.gen.gen.return_area_size.max(size);
        self.gen.gen.return_area_align = self.gen.gen.return_area_align.max(align);
        format!("{}RETURN_AREA", self.gen.gen.qualifier())
    }

    fn push_block(&mut self) {
        self.block_storage.push(BlockStorage {
            body: mem::take(&mut self.src),
            element: self.locals.tmp("element"),
            base: self.locals.tmp("base"),
            cleanup: mem::take(&mut self.cleanup),
        });
    }

    fn finish_block(&mut self, operands: &mut Vec<String>) {
        let BlockStorage {
            body,
            element,
            base,
            cleanup,
        } = self.block_storage.pop().unwrap();

        if !self.cleanup.is_empty() {
            self.needs_cleanup_list = true;

            for Cleanup {
                address,
                size,
                align,
            } in &self.cleanup
            {
                uwriteln!(
                    self.src,
                    "cleanupList.add(new {}Cleanup({address}, {size}, {align}));",
                    self.gen.gen.qualifier()
                );
            }
        }

        self.cleanup = cleanup;

        self.blocks.push(Block {
            body: mem::replace(&mut self.src, body),
            results: mem::take(operands),
            element,
            base,
        });
    }

    fn sizes(&self) -> &SizeAlign {
        &self.gen.gen.sizes
    }

    fn is_list_canonical(&self, _resolve: &Resolve, element: &Type) -> bool {
        is_primitive(element)
    }
}

fn perform_cast(op: &str, cast: &Bitcast) -> String {
    match cast {
        Bitcast::I32ToF32 => {
            format!("Float.intBitsToFloat({op})")
        }
        Bitcast::I64ToF32 => format!("Float.intBitsToFloat((int) ({op}))"),
        Bitcast::F32ToI32 => {
            format!("Float.floatToIntBits({op})")
        }
        Bitcast::F32ToI64 => format!("(long) Float.floatToIntBits({op})"),
        Bitcast::I64ToF64 => {
            format!("Double.longBitsToDouble({op})")
        }
        Bitcast::F64ToI64 => {
            format!("Double.doubleToLongBits({op})")
        }
        Bitcast::I32ToI64 => format!("(long) ({op})"),
        Bitcast::I64ToI32 => format!("(int) ({op})"),
        Bitcast::I64ToP64 => format!("{op}"),
        Bitcast::P64ToI64 => format!("{op}"),
        Bitcast::LToI64 | Bitcast::PToP64 => format!("(long) ({op})"),
        Bitcast::I64ToL | Bitcast::P64ToP => format!("(int) ({op})"),
        Bitcast::I32ToP
        | Bitcast::PToI32
        | Bitcast::I32ToL
        | Bitcast::LToI32
        | Bitcast::LToP
        | Bitcast::PToL
        | Bitcast::None => op.to_owned(),

        Bitcast::Sequence(sequence) => {
            let [first, second] = &**sequence;
            perform_cast(&perform_cast(op, first), second)
        }
    }
}

fn int_type(int: Int) -> &'static str {
    match int {
        Int::U8 => "byte",
        Int::U16 => "short",
        Int::U32 => "int",
        Int::U64 => "long",
    }
}

fn wasm_type(ty: WasmType) -> &'static str {
    match ty {
        WasmType::I32 => "int",
        WasmType::I64 => "long",
        WasmType::F32 => "float",
        WasmType::F64 => "double",
        WasmType::Pointer => "int",
        WasmType::PointerOrI64 => "long",
        WasmType::Length => "int",
    }
}

fn flags_repr(flags: &Flags) -> Int {
    match flags.repr() {
        FlagsRepr::U8 => Int::U8,
        FlagsRepr::U16 => Int::U16,
        FlagsRepr::U32(1) => Int::U32,
        FlagsRepr::U32(2) => Int::U64,
        repr => panic!("unimplemented flags {repr:?}"),
    }
}

fn list_element_info(ty: &Type) -> (usize, &'static str) {
    match ty {
        Type::U8 | Type::S8 => (1, "byte"),
        Type::U16 | Type::S16 => (2, "short"),
        Type::U32 | Type::S32 => (4, "int"),
        Type::U64 | Type::S64 => (8, "long"),
        Type::F32 => (4, "float"),
        Type::F64 => (8, "double"),
        _ => unreachable!(),
    }
}

fn indent(code: &str) -> String {
    let mut indented = String::with_capacity(code.len());
    let mut indent = 0;
    let mut was_empty = false;
    for line in code.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            if was_empty {
                continue;
            }
            was_empty = true;
        } else {
            was_empty = false;
        }

        if trimmed.starts_with('}') {
            indent -= 1;
        }
        indented.extend(iter::repeat(' ').take(indent * 4));
        indented.push_str(trimmed);
        if trimmed.ends_with('{') {
            indent += 1;
        }
        indented.push('\n');
    }
    indented
}

fn is_primitive(ty: &Type) -> bool {
    matches!(
        ty,
        Type::U8
            | Type::S8
            | Type::U16
            | Type::S16
            | Type::U32
            | Type::S32
            | Type::U64
            | Type::S64
            | Type::F32
            | Type::F64
    )
}

fn world_name(resolve: &Resolve, world: WorldId) -> String {
    format!(
        "wit.worlds.{}",
        resolve.worlds[world].name.to_upper_camel_case()
    )
}

fn interface_name(resolve: &Resolve, name: &WorldKey, direction: Direction) -> String {
    let pkg = match name {
        WorldKey::Name(_) => None,
        WorldKey::Interface(id) => {
            let pkg = resolve.interfaces[*id].package.unwrap();
            Some(resolve.packages[pkg].name.clone())
        }
    };

    let name = match name {
        WorldKey::Name(name) => name,
        WorldKey::Interface(id) => resolve.interfaces[*id].name.as_ref().unwrap(),
    }
    .to_upper_camel_case();

    format!(
        "wit.{}.{}{name}",
        match direction {
            Direction::Import => "imports",
            Direction::Export => "exports",
        },
        if let Some(name) = &pkg {
            format!(
                "{}.{}.",
                name.namespace.to_java_ident(),
                name.name.to_java_ident()
            )
        } else {
            String::new()
        }
    )
}

fn split_qualified_name(name: &str) -> (String, &str) {
    let tokens = name.split('.').collect::<Vec<_>>();

    let package = tokens
        .iter()
        .copied()
        .take(tokens.len() - 1)
        .collect::<Vec<_>>()
        .join(".");

    let name = tokens.last().unwrap();

    (package, name)
}

trait ToJavaIdent: ToOwned {
    fn to_java_ident(&self) -> Self::Owned;
}

impl ToJavaIdent for str {
    fn to_java_ident(&self) -> String {
        // Escape Java keywords
        // Source: https://docs.oracle.com/javase/tutorial/java/nutsandbolts/_keywords.html
        match self {
            "abstract" | "continue" | "for" | "new" | "switch" | "assert" | "default" | "goto"
            | "package" | "synchronized" | "boolean" | "do" | "if" | "private" | "this"
            | "break" | "double" | "implements" | "protected" | "throw" | "byte" | "else"
            | "import" | "public" | "throws" | "case" | "enum" | "instanceof" | "return"
            | "transient" | "catch" | "extends" | "int" | "short" | "try" | "char" | "final"
            | "interface" | "static" | "void" | "class" | "finally" | "long" | "strictfp"
            | "volatile" | "const" | "float" | "native" | "super" | "while" => format!("{self}_"),
            _ => self.to_lower_camel_case(),
        }
    }
}
