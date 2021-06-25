use heck::*;
use std::collections::{BTreeSet, HashMap};
use std::mem;
use witx_bindgen_gen_core::witx2::abi::{
    Bindgen, Bitcast, Direction, Instruction, LiftLower, WitxInstruction,
};
use witx_bindgen_gen_core::{witx2::*, Files, Generator};

#[derive(Default)]
pub struct Js {
    src: Source,
    opts: Opts,
    imports: HashMap<String, Vec<Import>>,
    exports: HashMap<String, Exports>,
    sizes: SizeAlign,
    needs_clamp_guest: bool,
    needs_clamp_host: bool,
    needs_clamp_host64: bool,
    needs_get_export: bool,
    needs_data_view: bool,
    needs_validate_f32: bool,
    needs_validate_f64: bool,
    needs_validate_guest_char: bool,
    needs_validate_host_char: bool,
    needs_i32_to_f32: bool,
    needs_f32_to_i32: bool,
    needs_i64_to_f64: bool,
    needs_f64_to_i64: bool,
    needs_utf8_decoder: bool,
    needs_utf8_encode: bool,
    needed_resources: BTreeSet<ResourceId>,
    needs_validate_flags: bool,
    needs_validate_flags64: bool,
    needs_push_buffer: bool,
    needs_pull_buffer: bool,
    needs_ty_option: bool,
    needs_ty_result: bool,
    needs_ty_push_buffer: bool,
    needs_ty_pull_buffer: bool,
}

struct Import {
    name: String,
    src: Source,
}

#[derive(Default)]
struct Exports {
    funcs: Vec<Source>,
}

#[derive(Default, Debug)]
#[cfg_attr(feature = "structopt", derive(structopt::StructOpt))]
pub struct Opts {
    #[cfg_attr(feature = "structopt", structopt(long = "no-typescript"))]
    pub no_typescript: bool,
}

impl Opts {
    pub fn build(self) -> Js {
        let mut r = Js::new();
        r.opts = self;
        r
    }
}

impl Js {
    pub fn new() -> Js {
        Js::default()
    }

    fn is_nullable_option(&self, iface: &Interface, variant: &Variant) -> bool {
        match variant.as_option() {
            Some(ty) => match ty {
                Type::Id(id) => match &iface.types[*id].kind {
                    TypeDefKind::Variant(v) => !self.is_nullable_option(iface, v),
                    _ => true,
                },
                _ => true,
            },
            None => false,
        }
    }

    fn array_ty(&self, iface: &Interface, ty: &Type) -> Option<&'static str> {
        match ty {
            Type::U8 | Type::CChar => Some("Uint8Array"),
            Type::S8 => Some("Int8Array"),
            Type::U16 => Some("Uint16Array"),
            Type::S16 => Some("Int16Array"),
            Type::U32 | Type::Usize => Some("Uint32Array"),
            Type::S32 => Some("Int32Array"),
            Type::U64 => Some("BigUint64Array"),
            Type::S64 => Some("BigInt64Array"),
            Type::F32 => Some("Float32Array"),
            Type::F64 => Some("Float64Array"),
            Type::Char => None,
            Type::Handle(_) => None,
            Type::Id(id) => match &iface.types[*id].kind {
                TypeDefKind::Type(t) => self.array_ty(iface, t),
                _ => None,
            },
        }
    }

    fn print_ty(&mut self, iface: &Interface, ty: &Type) {
        match ty {
            Type::U8
            | Type::CChar
            | Type::S8
            | Type::U16
            | Type::S16
            | Type::U32
            | Type::Usize
            | Type::S32
            | Type::F32
            | Type::F64 => self.src.ts("number"),
            Type::U64 | Type::S64 => self.src.ts("bigint"),
            Type::Char => self.src.ts("string"),
            Type::Handle(_) => self.src.ts("any"), // TODO
            Type::Id(id) => {
                let ty = &iface.types[*id];
                if let Some(name) = &ty.name {
                    return self.src.ts(&name.to_camel_case());
                }
                match &ty.kind {
                    TypeDefKind::Type(t) => self.print_ty(iface, t),
                    TypeDefKind::Record(r) if r.is_tuple() => self.print_tuple(iface, r),
                    TypeDefKind::Record(_) => panic!("anonymous record"),
                    TypeDefKind::Variant(v) if v.is_bool() => self.src.ts("boolean"),
                    TypeDefKind::Variant(v) => {
                        if self.is_nullable_option(iface, v) {
                            self.print_ty(iface, v.cases[1].ty.as_ref().unwrap());
                            self.src.ts(" | null");
                        } else if let Some(t) = v.as_option() {
                            self.needs_ty_option = true;
                            self.src.ts("Option<");
                            self.print_ty(iface, t);
                            self.src.ts(">");
                        } else if let Some((ok, err)) = v.as_expected() {
                            self.needs_ty_result = true;
                            self.src.ts("Result<");
                            match ok {
                                Some(ok) => self.print_ty(iface, ok),
                                None => self.src.ts("undefined"),
                            }
                            self.src.ts(", ");
                            match err {
                                Some(err) => self.print_ty(iface, err),
                                None => self.src.ts("undefined"),
                            }
                            self.src.ts(">");
                        } else {
                            panic!("anonymous variant");
                        }
                    }
                    TypeDefKind::List(v) => self.print_list(iface, v),
                    TypeDefKind::PushBuffer(v) => self.print_buffer(iface, true, v),
                    TypeDefKind::PullBuffer(v) => self.print_buffer(iface, false, v),
                    TypeDefKind::Pointer(_) | TypeDefKind::ConstPointer(_) => {
                        self.src.ts("number");
                    }
                }
            }
        }
    }

    fn print_list(&mut self, iface: &Interface, ty: &Type) {
        match self.array_ty(iface, ty) {
            Some(ty) => self.src.ts(ty),
            None => {
                if let Type::Char = ty {
                    self.src.ts("string");
                } else {
                    self.print_ty(iface, ty);
                    self.src.ts("[]");
                }
            }
        }
    }

    fn print_tuple(&mut self, iface: &Interface, record: &Record) {
        self.src.ts("[");
        for (i, field) in record.fields.iter().enumerate() {
            if i > 0 {
                self.src.ts(", ");
            }
            self.print_ty(iface, &field.ty);
        }
        self.src.ts("]");
    }

    fn print_buffer(&mut self, iface: &Interface, push: bool, ty: &Type) {
        match self.array_ty(iface, ty) {
            Some(ty) => self.src.ts(ty),
            None => {
                if push {
                    self.needs_ty_push_buffer = true;
                    self.src.ts("PushBuffer");
                } else {
                    self.needs_ty_pull_buffer = true;
                    self.src.ts("PullBuffer");
                }
                self.src.ts("<");
                self.print_ty(iface, ty);
                self.src.ts(">");
            }
        }
    }

    fn docs(&mut self, docs: &Docs) {
        let docs = match &docs.contents {
            Some(docs) => docs,
            None => return,
        };
        for line in docs.lines() {
            self.src.ts(&format!("// {}\n", line));
        }
    }

    fn ts_func(&mut self, iface: &Interface, func: &Function) {
        self.docs(&func.docs);
        self.src.ts(&func.name.to_snake_case());
        self.src.ts("(");
        for (i, (name, ty)) in func.params.iter().enumerate() {
            if i > 0 {
                self.src.ts(", ");
            }
            self.src.ts(to_js_ident(&name.to_snake_case()));
            self.src.ts(": ");
            self.print_ty(iface, ty);
        }
        self.src.ts("): ");
        match func.results.len() {
            0 => self.src.ts("void"),
            1 => self.print_ty(iface, &func.results[0].1),
            _ => {
                if func.results.iter().any(|(n, _)| n.is_empty()) {
                    self.src.ts("[");
                    for (i, (_, ty)) in func.results.iter().enumerate() {
                        if i > 0 {
                            self.src.ts(", ");
                        }
                        self.print_ty(iface, ty);
                    }
                    self.src.ts("]");
                } else {
                    self.src.ts("{ ");
                    for (i, (name, ty)) in func.results.iter().enumerate() {
                        if i > 0 {
                            self.src.ts(", ");
                        }
                        self.src.ts(&name.to_snake_case());
                        self.src.ts(": ");
                        self.print_ty(iface, ty);
                    }
                    self.src.ts(" }");
                }
            }
        }
        self.src.ts(";\n");
    }
}

impl Generator for Js {
    fn preprocess(&mut self, iface: &Interface, dir: Direction) {
        self.sizes.fill(dir, iface);
    }

    fn type_record(
        &mut self,
        iface: &Interface,
        _id: TypeId,
        name: &str,
        record: &Record,
        docs: &Docs,
    ) {
        self.docs(docs);
        if record.is_tuple() {
            self.src
                .ts(&format!("export type {} = ", name.to_camel_case()));
            self.print_tuple(iface, record);
            self.src.ts(";\n");
        } else if record.is_flags() {
            let repr = iface
                .flags_repr(record)
                .expect("unsupported number of flags");
            let suffix = if repr == Int::U64 {
                self.src
                    .ts(&format!("export type {} = bigint;\n", name.to_camel_case()));
                "n"
            } else {
                self.src
                    .ts(&format!("export type {} = number;\n", name.to_camel_case()));
                ""
            };
            let name = name.to_shouty_snake_case();
            for (i, field) in record.fields.iter().enumerate() {
                let field = field.name.to_shouty_snake_case();
                self.src.js(&format!(
                    "export const {}_{} = {}{};\n",
                    name,
                    field,
                    1u64 << i,
                    suffix,
                ));
                self.src.ts(&format!(
                    "export const {}_{} = {}{};\n",
                    name,
                    field,
                    1u64 << i,
                    suffix,
                ));
            }
        } else {
            self.src
                .ts(&format!("export interface {} {{\n", name.to_camel_case()));
            for field in record.fields.iter() {
                self.docs(&field.docs);
                self.src.ts(&format!("{}: ", field.name.to_snake_case()));
                self.print_ty(iface, &field.ty);
                self.src.ts(",\n");
            }
            self.src.ts("}\n");
        }
    }

    fn type_variant(
        &mut self,
        iface: &Interface,
        _id: TypeId,
        name: &str,
        variant: &Variant,
        docs: &Docs,
    ) {
        self.docs(docs);
        if variant.is_bool() {
            self.src.ts(&format!(
                "export type {} = boolean;\n",
                name.to_camel_case(),
            ));
        } else if self.is_nullable_option(iface, variant) {
            self.src
                .ts(&format!("export type {} = ", name.to_camel_case()));
            self.print_ty(iface, variant.cases[1].ty.as_ref().unwrap());
            self.src.ts(" | null;\n");
        } else if variant.is_enum() {
            self.src
                .ts(&format!("export enum {} {{\n", name.to_camel_case()));
            for case in variant.cases.iter() {
                self.docs(&case.docs);
                self.src.ts(&case.name.to_camel_case());
                self.src.ts(",\n");
            }
            self.src.ts("}\n");

            self.src.js(&format!(
                "export const {} = Object.freeze({{\n",
                name.to_camel_case()
            ));
            for (i, case) in variant.cases.iter().enumerate() {
                let name = case.name.to_camel_case();
                self.src.js(&format!("{}: \"{}\",\n", i, name));
                self.src.js(&format!("\"{}\": {},\n", name, i));
            }
            self.src.js("});\n");
        } else {
            self.src
                .ts(&format!("export type {} = ", name.to_camel_case()));
            for (i, case) in variant.cases.iter().enumerate() {
                if i > 0 {
                    self.src.ts(" | ");
                }
                self.src
                    .ts(&format!("{}_{}", name, case.name).to_camel_case());
            }
            self.src.ts(";\n");
            for case in variant.cases.iter() {
                self.docs(&case.docs);
                self.src.ts(&format!(
                    "export interface {} {{\n",
                    format!("{}_{}", name, case.name).to_camel_case()
                ));
                self.src.ts("tag: \"");
                self.src.ts(&case.name);
                self.src.ts("\",\n");
                if let Some(ty) = &case.ty {
                    self.src.ts("val: ");
                    self.print_ty(iface, ty);
                    self.src.ts(",\n");
                }
                self.src.ts("}\n");
            }
        }
    }

    fn type_resource(&mut self, iface: &Interface, ty: ResourceId) {
        // panic!()
        drop((iface, ty));
    }

    fn type_alias(&mut self, iface: &Interface, _id: TypeId, name: &str, ty: &Type, docs: &Docs) {
        self.docs(docs);
        self.src
            .ts(&format!("export type {} = ", name.to_camel_case()));
        self.print_ty(iface, ty);
        self.src.ts(";\n");
    }

    fn type_list(&mut self, iface: &Interface, _id: TypeId, name: &str, ty: &Type, docs: &Docs) {
        self.docs(docs);
        self.src
            .ts(&format!("export type {} = ", name.to_camel_case()));
        self.print_list(iface, ty);
        self.src.ts(";\n");
    }

    fn type_pointer(
        &mut self,
        iface: &Interface,
        _id: TypeId,
        name: &str,
        const_: bool,
        ty: &Type,
        docs: &Docs,
    ) {
        drop((iface, _id, name, const_, ty, docs));
    }

    fn type_builtin(&mut self, iface: &Interface, _id: TypeId, name: &str, ty: &Type, docs: &Docs) {
        drop((iface, _id, name, ty, docs));
    }

    fn type_push_buffer(
        &mut self,
        iface: &Interface,
        _id: TypeId,
        name: &str,
        ty: &Type,
        docs: &Docs,
    ) {
        self.docs(docs);
        self.src
            .ts(&format!("export type {} = ", name.to_camel_case()));
        self.print_buffer(iface, true, ty);
        self.src.ts(";\n");
    }

    fn type_pull_buffer(
        &mut self,
        iface: &Interface,
        _id: TypeId,
        name: &str,
        ty: &Type,
        docs: &Docs,
    ) {
        self.docs(docs);
        self.src
            .ts(&format!("export type {} = ", name.to_camel_case()));
        self.print_buffer(iface, false, ty);
        self.src.ts(";\n");
    }

    fn import(&mut self, iface: &Interface, func: &Function) {
        let prev = mem::take(&mut self.src);

        let sig = iface.wasm_signature(Direction::Import, func);
        let args = (0..sig.params.len())
            .map(|i| format!("arg{}", i))
            .collect::<Vec<_>>()
            .join(", ");
        self.src.js(&format!("function({}) {{\n", args));
        self.ts_func(iface, func);

        let mut f = FunctionBindgen::new(self, false);
        iface.call(
            Direction::Import,
            LiftLower::LiftArgsLowerResults,
            func,
            &mut f,
        );

        let FunctionBindgen {
            src,
            needs_memory,
            needs_realloc,
            needs_free,
            ..
        } = f;

        if needs_memory {
            self.needs_get_export = true;
            // TODO: hardcoding "memory"
            self.src.js("const memory = get_export(\"memory\");\n");
        }

        if let Some(name) = needs_realloc {
            self.needs_get_export = true;
            self.src
                .js(&format!("const realloc = get_export(\"{}\");\n", name));
        }

        if let Some(name) = needs_free {
            self.needs_get_export = true;
            self.src
                .js(&format!("const free = get_export(\"{}\");\n", name));
        }
        self.src.js(&src.js);
        self.src.js("}");

        let src = mem::replace(&mut self.src, prev);
        self.imports
            .entry(iface.name.to_string())
            .or_insert(Vec::new())
            .push(Import {
                name: func.name.to_string(),
                src,
            });
    }

    fn export(&mut self, iface: &Interface, func: &Function) {
        let prev = mem::take(&mut self.src);

        self.src.js(&format!(
            "{}({}) {{\n",
            func.name.to_snake_case(),
            func.params
                .iter()
                .enumerate()
                .map(|(i, _)| format!("arg{}", i))
                .collect::<Vec<_>>()
                .join(", ")
        ));
        self.ts_func(iface, func);

        let mut f = FunctionBindgen::new(self, false);
        iface.call(
            Direction::Export,
            LiftLower::LowerArgsLiftResults,
            func,
            &mut f,
        );

        let FunctionBindgen {
            src,
            needs_memory,
            needs_realloc,
            needs_free,
            ..
        } = f;
        if needs_memory {
            // TODO: hardcoding "memory"
            self.src.js("const memory = this._exports.memory;\n");
        }

        if let Some(name) = needs_realloc {
            self.src
                .js(&format!("const realloc = this._exports[\"{}\"];\n", name));
        }

        if let Some(name) = needs_free {
            self.src
                .js(&format!("const free = this._exports[\"{}\"];\n", name));
        }
        self.src.js(&src.js);
        self.src.js("}\n");

        let exports = self
            .exports
            .entry(iface.name.to_string())
            .or_insert_with(Exports::default);

        let func_body = mem::replace(&mut self.src, prev);
        exports.funcs.push(func_body);
    }

    fn finish(&mut self, iface: &Interface, files: &mut Files) {
        self.print_intrinsics();

        for (module, funcs) in mem::take(&mut self.imports) {
            let module = module.to_snake_case();
            // TODO: `module.exports` vs `export function`
            self.src.js(&format!(
                "export function add_{}_to_imports(imports, obj{}) {{\n",
                module,
                if self.needs_get_export {
                    ", get_export"
                } else {
                    ""
                },
            ));
            self.src.ts(&format!(
                "export function add_{}_to_imports(imports: any, obj: {}{}): void;\n",
                module,
                module.to_camel_case(),
                if self.needs_get_export {
                    ", get_export: (string) => WebAssembly.ExportValue"
                } else {
                    ""
                },
            ));
            self.src.js(&format!(
                "if (!(\"{0}\" in imports)) imports[\"{0}\"] = {{}};\n",
                module,
            ));

            self.src
                .ts(&format!("export interface {} {{\n", module.to_camel_case()));

            for f in funcs {
                let func = f.name.to_snake_case();
                self.src.js(&format!(
                    "imports[\"{}\"][\"{}\"] = {};\n",
                    module,
                    func,
                    f.src.js.trim(),
                ));
                self.src.ts(&f.src.ts);
            }

            if self.needed_resources.len() > 0 {
                self.src
                    .js("if (!(\"canonical_abi\" in imports)) imports[\"canonical_abi\"] = {};\n");
            }
            for resource in self.needed_resources.iter() {
                self.src.js(&format!(
                    "imports.canonical_abi[\"resource_drop_{}\"] = (i) => {{
                        const val = resources{}.remove(i);
                        if (obj.drop_{})
                            obj.drop_{2}(val);
                    }};\n",
                    iface.resources[*resource].name,
                    resource.index(),
                    iface.resources[*resource].name.to_snake_case(),
                ));
                self.src.ts(&format!(
                    "drop_{}?: (any) => void;\n",
                    iface.resources[*resource].name.to_snake_case()
                ));
            }
            self.src.js("}");
            self.src.ts("}\n");
        }

        for (module, exports) in mem::take(&mut self.exports) {
            let module = module.to_camel_case();
            // TODO: `module.exports` vs `export function`
            self.src.js(&format!("export class {} {{\n", module));

            self.src.js("static async instantiate(module, imports) {\n");
            self.src.js(&format!("const me = new {}();\n", module));
            self.src.js("
                let ret;
                if (module instanceof WebAssembly.Module) {
                    ret = {
                        module,
                        instance: await WebAssembly.instantiate(module, imports),
                    };
                } else if (module instanceof ArrayBuffer || module instanceof Uint8Array) {
                    ret = await WebAssembly.instantiate(module, imports);
                } else {
                    ret = await WebAssembly.instantiateStreaming(module, imports);
                }
                me.module = ret.module;
                me.instance = ret.instance;
                me._exports = me.instance.exports;
                return me;
            ");
            self.src.js("}\n");

            self.src.ts(&format!("export class {} {{\n", module));
            self.src.ts(&format!(
                "static instantiate(module: WebAssembly.Module | BufferSource | Promise<Response> | Response, imports: any): Promise<{}>;\n",
                module
            ));
            self.src.ts("instance: WebAssembly.Instance;\n");
            self.src.ts("module: WebAssembly.Module;\n");

            for func in exports.funcs.iter() {
                self.src.js(&func.js);
                self.src.ts(&func.ts);
            }
            self.src.ts("}\n");
            self.src.js("}");
        }

        files.push("bindings.js", self.src.js.as_bytes());
        if !self.opts.no_typescript {
            files.push("bindings.d.ts", self.src.ts.as_bytes());
        }
    }
}

struct FunctionBindgen<'a> {
    gen: &'a mut Js,
    tmp: usize,
    src: Source,
    block_storage: Vec<witx_bindgen_gen_core::Source>,
    blocks: Vec<(String, Vec<String>)>,
    in_import: bool,
    needs_memory: bool,
    needs_realloc: Option<String>,
    needs_free: Option<String>,
}

impl FunctionBindgen<'_> {
    fn new(gen: &mut Js, in_import: bool) -> FunctionBindgen<'_> {
        FunctionBindgen {
            gen,
            tmp: 0,
            src: Source::default(),
            block_storage: Vec::new(),
            blocks: Vec::new(),
            in_import,
            needs_memory: false,
            needs_realloc: None,
            needs_free: None,
        }
    }

    fn tmp(&mut self) -> usize {
        let ret = self.tmp;
        self.tmp += 1;
        ret
    }

    fn clamp_guest<T>(&mut self, results: &mut Vec<String>, operands: &[String], min: T, max: T)
    where
        T: std::fmt::Display,
    {
        self.gen.needs_clamp_guest = true;
        results.push(format!("clamp_guest({}, {}, {})", operands[0], min, max));
    }

    fn clamp_host<T>(&mut self, results: &mut Vec<String>, operands: &[String], min: T, max: T)
    where
        T: std::fmt::Display,
    {
        self.gen.needs_clamp_host = true;
        results.push(format!("clamp_host({}, {}, {})", operands[0], min, max));
    }

    fn clamp_host64<T>(&mut self, results: &mut Vec<String>, operands: &[String], min: T, max: T)
    where
        T: std::fmt::Display,
    {
        self.gen.needs_clamp_host64 = true;
        results.push(format!("clamp_host64({}, {}n, {}n)", operands[0], min, max));
    }

    fn load(&mut self, method: &str, offset: i32, operands: &[String], results: &mut Vec<String>) {
        self.needs_memory = true;
        self.gen.needs_data_view = true;
        results.push(format!(
            "data_view(memory).{}({} + {}, true)",
            method, operands[0], offset,
        ));
    }

    fn store(&mut self, method: &str, offset: i32, operands: &[String]) {
        self.needs_memory = true;
        self.gen.needs_data_view = true;
        self.src.js(&format!(
            "data_view(memory).{}({} + {}, {}, true);\n",
            method, operands[1], offset, operands[0]
        ));
    }
}

impl Bindgen for FunctionBindgen<'_> {
    type Operand = String;

    fn sizes(&self) -> &SizeAlign {
        &self.gen.sizes
    }

    fn push_block(&mut self) {
        let prev = mem::take(&mut self.src.js);
        self.block_storage.push(prev);
    }

    fn finish_block(&mut self, operands: &mut Vec<String>) {
        let to_restore = self.block_storage.pop().unwrap();
        let src = mem::replace(&mut self.src.js, to_restore);
        self.blocks.push((src.into(), mem::take(operands)));
    }

    fn allocate_typed_space(&mut self, _iface: &Interface, _ty: TypeId) -> String {
        unimplemented!()
    }

    fn i64_return_pointer_area(&mut self, _amt: usize) -> String {
        unimplemented!()
    }

    fn is_list_canonical(&self, iface: &Interface, ty: &Type) -> bool {
        self.gen.array_ty(iface, ty).is_some()
    }

    fn emit(
        &mut self,
        iface: &Interface,
        inst: &Instruction<'_>,
        operands: &mut Vec<String>,
        results: &mut Vec<String>,
    ) {
        match inst {
            Instruction::GetArg { nth } => results.push(format!("arg{}", nth)),
            Instruction::I32Const { val } => results.push(val.to_string()),
            Instruction::ConstZero { tys } => {
                for _ in tys.iter() {
                    results.push("0".to_string());
                }
            }

            // The representation of i32 in JS is a number, so 8/16-bit values
            // get further clamped to ensure that the upper bits aren't set when
            // we pass the value, ensuring that only the right number of bits
            // are transferred.
            Instruction::U8FromI32 => self.clamp_guest(results, operands, u8::MIN, u8::MAX),
            Instruction::S8FromI32 => self.clamp_guest(results, operands, i8::MIN, i8::MAX),
            Instruction::U16FromI32 => self.clamp_guest(results, operands, u16::MIN, u16::MAX),
            Instruction::S16FromI32 => self.clamp_guest(results, operands, i16::MIN, i16::MAX),
            // Use `>>>0` to ensure the bits of the number are treated as
            // unsigned.
            Instruction::U32FromI32 | Instruction::UsizeFromI32 => {
                results.push(format!("{} >>> 0", operands[0]));
            }
            // All bigints coming from wasm are treated as signed, so convert
            // it to ensure it's treated as unsigned.
            Instruction::U64FromI64 => results.push(format!("BigInt.asUintN(64, {})", operands[0])),
            // Nothing to do signed->signed where the representations are the
            // same.
            Instruction::S32FromI32 | Instruction::S64FromI64 => {
                results.push(operands.pop().unwrap())
            }

            // All values coming from the host and going to wasm need to have
            // their ranges validated, since the host could give us any value.
            Instruction::I32FromU8 => self.clamp_host(results, operands, u8::MIN, u8::MAX),
            Instruction::I32FromS8 => self.clamp_host(results, operands, i8::MIN, i8::MAX),
            Instruction::I32FromU16 => self.clamp_host(results, operands, u16::MIN, u16::MAX),
            Instruction::I32FromS16 => self.clamp_host(results, operands, i16::MIN, i16::MAX),
            Instruction::I32FromU32 | Instruction::I32FromUsize => {
                self.clamp_host(results, operands, u32::MIN, u32::MAX);
            }
            Instruction::I32FromS32 => self.clamp_host(results, operands, i32::MIN, i32::MAX),
            Instruction::I64FromU64 => self.clamp_host64(results, operands, u64::MIN, u64::MAX),
            Instruction::I64FromS64 => self.clamp_host64(results, operands, i64::MIN, i64::MAX),

            // The native representation in JS of f32 and f64 is just a number,
            // so there's nothing to do here. Everything wasm gives us is
            // representable in JS.
            Instruction::If32FromF32 | Instruction::If64FromF64 => {
                results.push(operands.pop().unwrap())
            }

            // For f32 coming from the host we need to validate that the value
            // is indeed a number and that the 32-bit value matches the
            // original value.
            Instruction::F32FromIf32 => {
                self.gen.needs_validate_f32 = true;
                results.push(format!("validate_f32({})", operands[0]));
            }

            // Similar to f32, but no range checks, just checks it's a number
            Instruction::F64FromIf64 => {
                self.gen.needs_validate_f64 = true;
                results.push(format!("validate_f64({})", operands[0]));
            }

            // Validate that i32 values coming from wasm are indeed valid code
            // points.
            Instruction::CharFromI32 => {
                self.gen.needs_validate_guest_char = true;
                results.push(format!("validate_guest_char({})", operands[0]));
            }

            // Validate that strings are indeed 1 character long and valid
            // unicode.
            Instruction::I32FromChar => {
                self.gen.needs_validate_host_char = true;
                results.push(format!("validate_host_char({})", operands[0]));
            }

            Instruction::Bitcasts { casts } => {
                for (cast, op) in casts.iter().zip(operands) {
                    match cast {
                        Bitcast::I32ToF32 => {
                            self.gen.needs_i32_to_f32 = true;
                            results.push(format!("i32ToF32({})", op));
                        }
                        Bitcast::F32ToI32 => {
                            self.gen.needs_f32_to_i32 = true;
                            results.push(format!("f32ToI32({})", op));
                        }
                        Bitcast::F32ToF64 | Bitcast::F64ToF32 => results.push(op.clone()),
                        Bitcast::I64ToF64 => {
                            self.gen.needs_i64_to_f64 = true;
                            results.push(format!("i64ToF64({})", op));
                        }
                        Bitcast::F64ToI64 => {
                            self.gen.needs_f64_to_i64 = true;
                            results.push(format!("f64ToI64({})", op));
                        }
                        Bitcast::I32ToI64 => results.push(format!("BigInt({})", op)),
                        Bitcast::I64ToI32 => results.push(format!("Number({})", op)),
                        Bitcast::I64ToF32 => {
                            self.gen.needs_i32_to_f32 = true;
                            results.push(format!("i32ToF32(Number({}))", op));
                        }
                        Bitcast::F32ToI64 => {
                            self.gen.needs_f32_to_i32 = true;
                            results.push(format!("BigInt(f32ToI32({}))", op));
                        }
                        Bitcast::None => results.push(op.clone()),
                    }
                }
            }

            Instruction::I32FromOwnedHandle { ty } => {
                self.gen.needed_resources.insert(*ty);
                results.push(format!("resources{}.insert({})", ty.index(), operands[0]));
            }
            Instruction::HandleBorrowedFromI32 { ty } => {
                self.gen.needed_resources.insert(*ty);
                results.push(format!("resources{}.get({})", ty.index(), operands[0]));
            }
            //    Instruction::I32FromBorrowedHandle { .. } => {
            //        results.push(format!("{}.0", operands[0]));
            //    }
            //    Instruction::HandleOwnedFromI32 { ty } => {
            //        let name = &iface.resources[*ty].name;
            //        results.push(format!(
            //            "{}({}, std::mem::ManuallyDrop::new(self.{}_close.clone()))",
            //            name.to_camel_case(),
            //            operands[0],
            //            name.to_snake_case(),
            //        ));
            //    }
            Instruction::RecordLower { record, .. } => {
                if record.is_tuple() {
                    // Tuples are represented as an array, sowe can use
                    // destructuring assignment to lower the tuple into its
                    // components.
                    let tmp = self.tmp();
                    let mut expr = "const [".to_string();
                    for i in 0..record.fields.len() {
                        if i > 0 {
                            expr.push_str(", ");
                        }
                        let name = format!("tuple{}_{}", tmp, i);
                        expr.push_str(&name);
                        results.push(name);
                    }
                    self.src.js(&format!("{}] = {};\n", expr, operands[0]));
                } else {
                    // Otherwise we use destructuring field access to get each
                    // field individually.
                    let tmp = self.tmp();
                    let mut expr = "const {".to_string();
                    for (i, field) in record.fields.iter().enumerate() {
                        if i > 0 {
                            expr.push_str(", ");
                        }
                        let name = format!("v{}_{}", tmp, i);
                        expr.push_str(&field.name.to_snake_case());
                        expr.push_str(": ");
                        expr.push_str(&name);
                        results.push(name);
                    }
                    self.src.js(&format!("{} }} = {};\n", expr, operands[0]));
                }
            }

            Instruction::RecordLift { record, .. } => {
                if record.is_tuple() {
                    // Tuples are represented as an array, so we just shove all
                    // the operands into an array.
                    results.push(format!("[{}]", operands.join(", ")));
                } else {
                    // Otherwise records are represented as plain objects, so we
                    // make a new object and set all the fields with an object
                    // literal.
                    let mut result = "{\n".to_string();
                    for (field, op) in record.fields.iter().zip(operands) {
                        result.push_str(&format!("{}: {},\n", field.name.to_snake_case(), op));
                    }
                    result.push_str("}");
                    results.push(result);
                }
            }

            Instruction::FlagsLower { record, .. } | Instruction::FlagsLift { record, .. } => {
                match record.num_i32s() {
                    0 | 1 => {
                        self.gen.needs_validate_flags = true;
                        let mask = (1u64 << record.fields.len()) - 1;
                        results.push(format!("validate_flags({}, {})", operands[0], mask));
                    }
                    _ => panic!("unsupported bitflags"),
                }
            }
            Instruction::FlagsLower64 { record, .. } | Instruction::FlagsLift64 { record, .. } => {
                self.gen.needs_validate_flags64 = true;
                let mask = (1u128 << record.fields.len()) - 1;
                results.push(format!("validate_flags64({}, {}n)", operands[0], mask));
            }

            Instruction::VariantPayload => results.push("e".to_string()),
            Instruction::VariantLower {
                variant,
                nresults,
                name,
                ..
            } => {
                let blocks = self
                    .blocks
                    .drain(self.blocks.len() - variant.cases.len()..)
                    .collect::<Vec<_>>();
                let tmp = self.tmp();
                self.src
                    .js(&format!("const variant{} = {};\n", tmp, operands[0]));

                if *nresults == 1 && variant.is_enum() && name.is_some() && !variant.is_bool() {
                    let name = name.unwrap().to_camel_case();
                    self.src
                        .js(&format!("if (!(variant{} in {}))\n", tmp, name));
                    self.src.js(&format!(
                        "throw new RangeError(\"invalid variant specified for {}\");\n",
                        name,
                    ));
                    results.push(format!(
                        "Number.isInteger(variant{}) ? variant{0} : {}[variant{0}]",
                        tmp, name
                    ));
                    return;
                }

                for i in 0..*nresults {
                    self.src.js(&format!("let variant{}_{};\n", tmp, i));
                    results.push(format!("variant{}_{}", tmp, i));
                }

                let expr_to_match = if variant.is_bool()
                    || self.gen.is_nullable_option(iface, variant)
                    || (variant.is_enum() && name.is_some())
                {
                    format!("variant{}", tmp)
                } else {
                    format!("variant{}.tag", tmp)
                };

                self.src.js(&format!("switch ({}) {{\n", expr_to_match));
                let mut use_default = true;
                for (i, (case, (block, block_results))) in
                    variant.cases.iter().zip(blocks).enumerate()
                {
                    if variant.is_bool() {
                        self.src.js(&format!("case {}: {{\n", case.name.as_str()));
                    } else if self.gen.is_nullable_option(iface, variant) {
                        if case.ty.is_none() {
                            self.src.js("case null: {\n");
                        } else {
                            self.src.js("default: {\n");
                            self.src.js(&format!("const e = variant{};\n", tmp));
                            use_default = false;
                        }
                    } else if variant.is_enum() && name.is_some() {
                        self.src.js(&format!("case {}: {{\n", i));
                        self.src.js(&format!("const e = variant{};\n", tmp));
                    } else {
                        self.src
                            .js(&format!("case \"{}\": {{\n", case.name.as_str()));
                        if case.ty.is_some() {
                            self.src.js(&format!("const e = variant{}.val;\n", tmp));
                        }
                    };
                    self.src.js(&block);

                    for (i, result) in block_results.iter().enumerate() {
                        self.src
                            .js(&format!("variant{}_{} = {};\n", tmp, i, result));
                    }
                    self.src.js("break;\n}\n");
                }
                if use_default {
                    let variant_name = name.map(|s| s.to_camel_case());
                    let variant_name = variant_name.as_deref().unwrap_or_else(|| {
                        if variant.is_bool() {
                            "bool"
                        } else if variant.as_expected().is_some() {
                            "expected"
                        } else if variant.as_option().is_some() {
                            "option"
                        } else {
                            unimplemented!()
                        }
                    });
                    self.src.js("default:\n");
                    self.src.js(&format!(
                        "throw new RangeError(\"invalid variant specified for {}\");\n",
                        variant_name
                    ));
                }
                self.src.js("}\n");
            }

            Instruction::VariantLift { variant, name, .. } => {
                let blocks = self
                    .blocks
                    .drain(self.blocks.len() - variant.cases.len()..)
                    .collect::<Vec<_>>();

                let tmp = self.tmp();
                if variant.is_enum() && name.is_some() && !variant.is_bool() {
                    let name = name.unwrap().to_camel_case();
                    self.src
                        .js(&format!("const tag{} = {};\n", tmp, operands[0]));
                    self.src.js(&format!("if (!(tag{} in {}))\n", tmp, name));
                    self.src.js(&format!(
                        "throw new RangeError(\"invalid discriminant specified for {}\");\n",
                        name,
                    ));
                    results.push(format!("tag{}", tmp));
                    return;
                }

                self.src.js(&format!("let variant{};\n", tmp));
                self.src.js(&format!("switch ({}) {{\n", operands[0]));
                for (i, (case, (block, block_results))) in
                    variant.cases.iter().zip(blocks).enumerate()
                {
                    self.src.js(&format!("case {}: {{\n", i));
                    self.src.js(&block);

                    if variant.is_bool() {
                        assert!(block_results.is_empty());
                        self.src
                            .js(&format!("variant{} = {};\n", tmp, case.name.as_str()));
                    } else if variant.is_enum() && name.is_some() {
                        assert!(block_results.is_empty());
                        self.src.js(&format!("variant{} = tag{0};\n", tmp));
                    } else if self.gen.is_nullable_option(iface, variant) {
                        if case.ty.is_none() {
                            assert!(block_results.is_empty());
                            self.src.js(&format!("variant{} = null;\n", tmp));
                        } else {
                            assert!(block_results.len() == 1);
                            self.src
                                .js(&format!("variant{} = {};\n", tmp, block_results[0]));
                        }
                    } else {
                        self.src.js(&format!("variant{} = {{\n", tmp));
                        self.src.js(&format!("tag: \"{}\",\n", case.name.as_str()));
                        if case.ty.is_some() {
                            assert!(block_results.len() == 1);
                            self.src.js(&format!("val: {},\n", block_results[0]));
                        } else {
                            assert!(block_results.is_empty());
                        }
                        self.src.js("};\n");
                    }
                    self.src.js("break;\n}\n");
                }
                let variant_name = name.map(|s| s.to_camel_case());
                let variant_name = variant_name.as_deref().unwrap_or_else(|| {
                    if variant.is_bool() {
                        "bool"
                    } else if variant.as_expected().is_some() {
                        "expected"
                    } else if variant.as_option().is_some() {
                        "option"
                    } else {
                        unimplemented!()
                    }
                });
                self.src.js("default:\n");
                self.src.js(&format!(
                    "throw new RangeError(\"invalid variant discriminant for {}\");\n",
                    variant_name
                ));
                self.src.js("}\n");
                results.push(format!("variant{}", tmp));
            }

            Instruction::ListCanonLower { element, realloc } => {
                // Lowering only happens when we're passing lists into wasm,
                // which forces us to always allocate, so this should always be
                // `Some`.
                let realloc = realloc.unwrap();
                self.gen.needs_get_export = true;
                self.needs_memory = true;
                self.needs_realloc = Some(realloc.to_string());
                let tmp = self.tmp();

                match element {
                    Type::Char => {
                        self.gen.needs_utf8_encode = true;
                        self.src.js(&format!(
                            "const ptr{} = utf8_encode({}, realloc, memory);\n",
                            tmp, operands[0],
                        ));
                        self.src
                            .js(&format!("const len{} = UTF8_ENCODED_LEN;\n", tmp));
                    }
                    _ => {
                        let size = self.gen.sizes.size(element);
                        let align = self.gen.sizes.align(element);
                        self.src
                            .js(&format!("const val{} = {};\n", tmp, operands[0]));
                        self.src.js(&format!("const len{} = val{0}.length;\n", tmp));
                        self.src.js(&format!(
                            "const ptr{} = realloc(0, 0, len{0} * {}, {});\n",
                            tmp, size, align
                        ));
                        self.src.js(&format!(
                            "(new Uint8Array(memory.buffer, ptr{}, len{0} * {})).set(new Uint8Array(val{0}));\n",
                            tmp, size,
                        ));
                    }
                };
                results.push(format!("ptr{}", tmp));
                results.push(format!("len{}", tmp));
            }
            Instruction::ListCanonLift { element, free } => {
                self.needs_memory = true;
                let tmp = self.tmp();
                self.src
                    .js(&format!("const ptr{} = {};\n", tmp, operands[0]));
                self.src
                    .js(&format!("const len{} = {};\n", tmp, operands[1]));
                let (result, align) = match element {
                    Type::Char => {
                        self.gen.needs_utf8_decoder = true;
                        (
                            format!(
                                "UTF8_DECODER.decode(new Uint8Array(memory.buffer, ptr{}, len{0}))",
                                tmp,
                            ),
                            1,
                        )
                    }
                    _ => {
                        let array_ty = self.gen.array_ty(iface, element).unwrap();
                        (
                            format!(
                                "new {}(memory.buffer.slice(ptr{}, ptr{1} + len{1} * {}))",
                                array_ty,
                                tmp,
                                self.gen.sizes.size(element),
                            ),
                            self.gen.sizes.align(element),
                        )
                    }
                };
                match free {
                    Some(free) => {
                        self.needs_free = Some(free.to_string());
                        self.src.js(&format!("const list{} = {};\n", tmp, result));
                        self.src
                            .js(&format!("free(ptr{}, len{0}, {});\n", tmp, align));
                        results.push(format!("list{}", tmp));
                    }
                    None => results.push(result),
                }
            }

            Instruction::ListLower { element, realloc } => {
                let realloc = realloc.unwrap();
                let (body, body_results) = self.blocks.pop().unwrap();
                assert!(body_results.is_empty());
                let tmp = self.tmp();
                let vec = format!("vec{}", tmp);
                let result = format!("result{}", tmp);
                let len = format!("len{}", tmp);
                self.needs_realloc = Some(realloc.to_string());
                let size = self.gen.sizes.size(element);
                let align = self.gen.sizes.align(element);

                // first store our vec-to-lower in a temporary since we'll
                // reference it multiple times.
                self.src.js(&format!("const {} = {};\n", vec, operands[0]));
                self.src.js(&format!("const {} = {}.length;\n", len, vec));

                // ... then realloc space for the result in the guest module
                self.src.js(&format!(
                    "const {} = realloc(0, 0, {} * {}, {});\n",
                    result, len, size, align,
                ));

                // ... then consume the vector and use the block to lower the
                // result.
                self.src
                    .js(&format!("for (let i = 0; i < {}.length; i++) {{\n", vec));
                self.src.js(&format!("const e = {}[i];\n", vec));
                self.src
                    .js(&format!("const base = {} + i * {};\n", result, size));
                self.src.js(&body);
                self.src.js("}\n");

                results.push(result);
                results.push(len);
            }

            Instruction::ListLift { element, free } => {
                let (body, body_results) = self.blocks.pop().unwrap();
                let tmp = self.tmp();
                let size = self.gen.sizes.size(element);
                let align = self.gen.sizes.align(element);
                let len = format!("len{}", tmp);
                self.src.js(&format!("const {} = {};\n", len, operands[1]));
                let base = format!("base{}", tmp);
                self.src.js(&format!("const {} = {};\n", base, operands[0]));
                let result = format!("result{}", tmp);
                self.src.js(&format!("const {} = [];\n", result));
                results.push(result.clone());

                self.src
                    .js(&format!("for (let i = 0; i < {}; i++) {{\n", len));
                self.src
                    .js(&format!("const base = {} + i * {};\n", base, size));
                self.src.js(&body);
                assert_eq!(body_results.len(), 1);
                self.src
                    .js(&format!("{}.push({});\n", result, body_results[0]));
                self.src.js("}\n");

                if let Some(free) = free {
                    self.needs_free = Some(free.to_string());
                    self.src
                        .js(&format!("free({}, {} * {}, {});\n", base, len, size, align,));
                }
            }

            Instruction::IterElem => results.push("e".to_string()),

            Instruction::IterBasePointer => results.push("base".to_string()),

            Instruction::BufferLiftPtrLen { push, ty } => {
                let (block, block_results) = self.blocks.pop().unwrap();
                // assert_eq!(block_results.len(), 1);
                let tmp = self.tmp();
                self.needs_memory = true;
                self.src
                    .js(&format!("const ptr{} = {};\n", tmp, operands[1]));
                self.src
                    .js(&format!("const len{} = {};\n", tmp, operands[2]));
                if let Some(ty) = self.gen.array_ty(iface, ty) {
                    results.push(format!("new {}(memory.buffer, ptr{}, len{1})", ty, tmp));
                } else {
                    let size = self.gen.sizes.size(ty);
                    if *push {
                        self.gen.needs_push_buffer = true;
                        assert!(block_results.is_empty());
                        results.push(format!(
                            "new PushBuffer(ptr{}, len{0}, {}, (e, base) => {{
                                {}
                            }})",
                            tmp, size, block
                        ));
                    } else {
                        self.gen.needs_pull_buffer = true;
                        assert_eq!(block_results.len(), 1);
                        results.push(format!(
                            "new PullBuffer(ptr{}, len{0}, {}, (base) => {{
                                {}
                                return {};
                            }})",
                            tmp, size, block, block_results[0],
                        ));
                    }
                }
            }

            //    Instruction::BufferLowerHandle { push, ty } => {
            //        let block = self.blocks.pop().unwrap();
            //        let size = self.sizes.size(ty);
            //        let tmp = self.tmp();
            //        let handle = format!("handle{}", tmp);
            //        let closure = format!("closure{}", tmp);
            //        self.needs_buffer_transaction = true;
            //        if iface.all_bits_valid(ty) {
            //            let method = if *push { "push_out_raw" } else { "push_in_raw" };
            //            self.push_str(&format!(
            //                "let {} = unsafe {{ buffer_transaction.{}({}) }};\n",
            //                handle, method, operands[0],
            //            ));
            //        } else if *push {
            //            self.closures.push_str(&format!(
            //                "let {} = |memory: &wasmtime::Memory, base: i32| {{
            //                    Ok(({}, {}))
            //                }};\n",
            //                closure, block, size,
            //            ));
            //            self.push_str(&format!(
            //                "let {} = unsafe {{ buffer_transaction.push_out({}, &{}) }};\n",
            //                handle, operands[0], closure,
            //            ));
            //        } else {
            //            let start = self.src.len();
            //            self.print_ty(iface, ty, TypeMode::AllBorrowed("'_"));
            //            let ty = self.src[start..].to_string();
            //            self.src.truncate(start);
            //            self.closures.push_str(&format!(
            //                "let {} = |memory: &wasmtime::Memory, base: i32, e: {}| {{
            //                    {};
            //                    Ok({})
            //                }};\n",
            //                closure, ty, block, size,
            //            ));
            //            self.push_str(&format!(
            //                "let {} = unsafe {{ buffer_transaction.push_in({}, &{}) }};\n",
            //                handle, operands[0], closure,
            //            ));
            //        }
            //        results.push(format!("{}", handle));
            //    }
            Instruction::CallWasm {
                module: _,
                name,
                sig,
            } => {
                match sig.results.len() {
                    0 => {}
                    1 => {
                        self.src.js("const ret = ");
                        results.push("ret".to_string());
                    }
                    n => {
                        self.src.js("const [");
                        for i in 0..n {
                            if i > 0 {
                                self.src.js(", ");
                            }
                            self.src.js(&format!("ret{}", i));
                            results.push(format!("ret{}", i));
                        }
                        self.src.js("] = ");
                    }
                }
                self.src.js("this._exports['");
                self.src.js(&name);
                self.src.js("'](");
                self.src.js(&operands.join(", "));
                self.src.js(");\n");
            }

            Instruction::CallInterface { module: _, func } => {
                if func.results.len() > 0 {
                    if func.results.len() == 1 {
                        self.src.js("const ret = ");
                        results.push("ret".to_string());
                    } else if func.results.iter().any(|p| p.0.is_empty()) {
                        self.src.js("const [");
                        for i in 0..func.results.len() {
                            if i > 0 {
                                self.src.js(", ")
                            }
                            let name = format!("ret{}", i);
                            self.src.js(&name);
                            results.push(name);
                        }
                        self.src.js("] = ");
                    } else {
                        self.src.js("const {");
                        for (i, (name, _)) in func.results.iter().enumerate() {
                            if i > 0 {
                                self.src.js(", ")
                            }
                            self.src.js(name);
                            results.push(name.clone());
                        }
                        self.src.js("} = ");
                    }
                }
                self.src.js("obj.");
                self.src.js(&func.name.to_snake_case());
                self.src.js("(");
                self.src.js(&operands.join(", "));
                self.src.js(");\n");
            }

            Instruction::Return { amt, func } => match amt {
                0 => {}
                1 => self.src.js(&format!("return {};\n", operands[0])),
                _ => {
                    if self.in_import || func.results.iter().any(|p| p.0.is_empty()) {
                        self.src.js(&format!("return [{}];\n", operands.join(", ")));
                    } else {
                        assert_eq!(func.results.len(), operands.len());
                        self.src.js(&format!(
                            "return {{ {} }};\n",
                            func.results
                                .iter()
                                .zip(operands)
                                .map(|((name, _), op)| format!("{}: {}", name.to_snake_case(), op))
                                .collect::<Vec<_>>()
                                .join(", ")
                        ));
                    }
                }
            },

            Instruction::I32Load { offset } => self.load("getInt32", *offset, operands, results),
            Instruction::I64Load { offset } => self.load("getBigInt64", *offset, operands, results),
            Instruction::F32Load { offset } => self.load("getFloat32", *offset, operands, results),
            Instruction::F64Load { offset } => self.load("getFloat64", *offset, operands, results),
            Instruction::I32Load8U { offset } => self.load("getUint8", *offset, operands, results),
            Instruction::I32Load8S { offset } => self.load("getInt8", *offset, operands, results),
            Instruction::I32Load16U { offset } => {
                self.load("getUint16", *offset, operands, results)
            }
            Instruction::I32Load16S { offset } => self.load("getInt16", *offset, operands, results),
            Instruction::I32Store { offset } => self.store("setInt32", *offset, operands),
            Instruction::I64Store { offset } => self.store("setBigInt64", *offset, operands),
            Instruction::F32Store { offset } => self.store("setFloat32", *offset, operands),
            Instruction::F64Store { offset } => self.store("setFloat64", *offset, operands),
            Instruction::I32Store8 { offset } => self.store("setInt8", *offset, operands),
            Instruction::I32Store16 { offset } => self.store("setInt16", *offset, operands),

            Instruction::Witx { instr } => match instr {
                WitxInstruction::PointerFromI32 { .. } => results.push(operands[0].clone()),
                i => unimplemented!("{:?}", i),
            },

            i => unimplemented!("{:?}", i),
        }
    }
}

impl Js {
    fn print_intrinsics(&mut self) {
        if self.needs_clamp_guest {
            self.src.js("function clamp_guest(i, min, max) {
                if (i < min || i > max) \
                    throw new RangeError(`must be between ${min} and ${max}`);
                return i;
            }\n");
        }

        if self.needs_clamp_host {
            self.src.js("function clamp_host(i, min, max) {
                if (!Number.isInteger(i)) \
                    throw new TypeError(`must be an integer`);
                if (i < min || i > max) \
                    throw new RangeError(`must be between ${min} and ${max}`);
                return i;
            }\n");
        }
        if self.needs_clamp_host64 {
            self.src.js("function clamp_host64(i, min, max) {
                if (typeof i !== 'bigint') \
                    throw new TypeError(`must be a bigint`);
                if (i < min || i > max) \
                    throw new RangeError(`must be between ${min} and ${max}`);
                return i;
            }\n");
        }
        if self.needs_data_view {
            self.src
                .js("let DATA_VIEW = new DataView(new ArrayBuffer());\n");
            // TODO: hardcoded `memory`
            self.src.js("function data_view(mem) {
                if (DATA_VIEW.buffer !== mem.buffer) \
                    DATA_VIEW = new DataView(mem.buffer);
                return DATA_VIEW;
            }\n");
        }

        if self.needs_validate_f32 {
            // TODO: test removing the isNan test and make sure something fails
            self.src.js("function validate_f32(val) {
                if (typeof val !== 'number') \
                    throw new TypeError(`must be a number`);
                if (!Number.isNaN(val) && Math.fround(val) !== val) \
                    throw new RangeError(`must be representable as f32`);
                return val;
            }\n");
        }

        if self.needs_validate_f64 {
            self.src.js("function validate_f64(val) {
                if (typeof val !== 'number') \
                    throw new TypeError(`must be a number`);
                return val;
            }\n");
        }

        if self.needs_validate_guest_char {
            self.src.js("function validate_guest_char(i) {
                if ((i > 0x10ffff) || (i >= 0xd800 && i <= 0xdfff)) \
                    throw new RangeError(`not a valid char`);
                return String.fromCodePoint(i);
            }\n");
        }

        if self.needs_validate_host_char {
            // TODO: this is incorrect. It at least allows strings of length > 0
            // but it probably doesn't do the right thing for unicode or invalid
            // utf16 strings either.
            self.src.js("function validate_host_char(s) {
                if (typeof s !== 'string') \
                    throw new TypeError(`must be a string`);
                return s.codePointAt(0);
            }\n");
        }
        if self.needs_i32_to_f32 || self.needs_f32_to_i32 {
            self.src.js("
                const I32_TO_F32_I = new Int32Array(1);
                const I32_TO_F32_F = new Float32Array(I32_TO_F32_I.buffer);
            ");
            if self.needs_i32_to_f32 {
                self.src.js("
                    function i32ToF32(i) {
                        I32_TO_F32_I[0] = i;
                        return I32_TO_F32_F[0];
                    }
                ");
            }
            if self.needs_f32_to_i32 {
                self.src.js("
                    function f32ToI32(f) {
                        I32_TO_F32_F[0] = f;
                        return I32_TO_F32_I[0];
                    }
                ");
            }
        }
        if self.needs_i64_to_f64 || self.needs_f64_to_i64 {
            self.src.js("
                const I64_TO_F64_I = new BigInt64Array(1);
                const I64_TO_F64_F = new Float64Array(I64_TO_F64_I.buffer);
            ");
            if self.needs_i64_to_f64 {
                self.src.js("
                    function i64ToF64(i) {
                        I64_TO_F64_I[0] = i;
                        return I64_TO_F64_F[0];
                    }
                ");
            }
            if self.needs_f64_to_i64 {
                self.src.js("
                    function f64ToI64(f) {
                        I64_TO_F64_F[0] = f;
                        return I64_TO_F64_I[0];
                    }
                ");
            }
        }

        if self.needs_utf8_decoder {
            self.src
                .js("const UTF8_DECODER = new TextDecoder('utf-8');\n");
        }
        if self.needs_utf8_encode {
            self.src.js("
                let UTF8_ENCODED_LEN = 0;
                const UTF8_ENCODER = new TextEncoder('utf-8');

                function utf8_encode(s, realloc, memory) {
                    if (typeof s !== 'string') \
                        throw new TypeError('expected a string');

                    if (s.length === 0) {
                        UTF8_ENCODED_LEN = 0;
                        return 1;
                    }

                    let alloc_len = 0;
                    let ptr = 0;
                    let writtenTotal = 0;
                    while (s.length > 0) {
                        ptr = realloc(ptr, alloc_len, alloc_len + s.length, 1);
                        alloc_len += s.length;
                        const { read, written } = UTF8_ENCODER.encodeInto(
                            s,
                            new Uint8Array(memory.buffer, ptr + writtenTotal, alloc_len - writtenTotal),
                        );
                        writtenTotal += written;
                        s = s.slice(read);
                    }
                    if (alloc_len > writtenTotal)
                        ptr = realloc(ptr, alloc_len, writtenTotal, 1);
                    UTF8_ENCODED_LEN = writtenTotal;
                    return ptr;
                }
            ");
        }

        if self.needed_resources.len() > 0 {
            self.src.js("
                class Slab {
                    constructor() {
                        this.list = [];
                        this.len = 0;
                        this.head = 0;
                    }

                    insert(val) {
                        if (this.head >= this.list.length) {
                            this.list.push({
                                next: this.list.length + 1,
                                val: undefined,
                            });
                        }
                        const ret = this.head;
                        const slot = this.list[ret];
                        this.head = slot.next;
                        slot.next = -1;
                        slot.val = val;
                        return ret;
                    }

                    get(idx) {
                        if (idx >= this.list.length)
                            throw new RangeError('handle index not valid');
                        const slot = this.list[idx];
                        if (slot.next === -1)
                            return slot.val;
                        throw new RangeError('handle index not valid');
                    }

                    remove(idx) {
                        const ret = this.get(idx); // validate the slot
                        const slot = this.list[idx];
                        slot.val = undefined;
                        slot.next = this.head;
                        this.head = idx;
                        return ret;
                    }
                }
            ");
        }
        for r in self.needed_resources.iter() {
            self.src
                .js(&format!("const resources{} = new Slab();\n", r.index()));
        }

        if self.needs_validate_flags {
            self.src.js("
                function validate_flags(flags, mask) {
                    if (!Number.isInteger(flags)) \
                        throw new TypeError('flags were not an integer');
                    if ((flags & ~mask) != 0)
                        throw new TypeError('flags have extraneous bits set');
                    return flags;
                }
            ")
        }

        if self.needs_validate_flags64 {
            self.src.js("
                function validate_flags64(flags, mask) {
                    if (typeof flags !== 'bigint')
                        throw new TypeError('flags were not a bigint');
                    if ((flags & ~mask) != 0n)
                        throw new TypeError('flags have extraneous bits set');
                    return flags;
                }
            ")
        }

        if self.needs_push_buffer {
            self.src.js("
                class PushBuffer {
                    constructor(ptr, len, size, write) {
                        this._ptr = ptr;
                        this._len = len;
                        this._size = size;
                        this._write = write;
                    }

                    get length() {
                        return this._len;
                    }

                    push(val) {
                        if (this._len == 0)
                            return false;
                        this._len -= 1;
                        this._write(val, this._ptr);
                        this._ptr += this._size;
                        return true;
                    }
                }
            ")
        }
        if self.needs_pull_buffer {
            self.src.js("
                class PullBuffer {
                    constructor(ptr, len, size, read) {
                        this._len = len;
                        this._ptr = ptr;
                        this._size = size;
                        this._read = read;
                    }

                    get length() {
                        return this._len;
                    }

                    pull() {
                        if (this._len == 0)
                            return undefined;
                        this._len -= 1;
                        const ret = this._read(this._ptr);
                        this._ptr += this._size;
                        return ret;
                    }
                }
            ")
        }

        if self.needs_ty_option {
            self.src
                .ts("export type Option<T> = { tag: \"none\" } | { tag: \"some\", val; T };\n");
        }
        if self.needs_ty_result {
            self.src.ts(
                "export type Result<T, E> = { tag: \"ok\", val: T } | { tag: \"err\", val: E };\n",
            );
        }
        if self.needs_ty_push_buffer {
            self.src.ts("
                export class PushBuffer<T> {
                    length: number;
                    push(T): boolean;
                }
            ");
        }
        if self.needs_ty_pull_buffer {
            self.src.ts("
                export class PullBuffer<T> {
                    length: number;
                    pull(): T | undefined;
                }
            ");
        }
    }
}

pub fn to_js_ident(name: &str) -> &str {
    match name {
        "in" => "in_",
        "import" => "import_",
        s => s,
    }
}

#[derive(Default)]
struct Source {
    js: witx_bindgen_gen_core::Source,
    ts: witx_bindgen_gen_core::Source,
}

impl Source {
    fn js(&mut self, s: &str) {
        self.js.push_str(s);
    }
    fn ts(&mut self, s: &str) {
        self.ts.push_str(s);
    }
}
