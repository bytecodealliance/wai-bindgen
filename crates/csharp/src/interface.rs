use crate::csharp_ident::ToCSharpIdent;
use crate::function::FunctionBindgen;
use crate::function::ResourceInfo;
use crate::world_generator::CSharp;
use heck::{ToShoutySnakeCase, ToUpperCamelCase};
use std::collections::{HashMap, HashSet};
use std::fmt::Write;
use std::ops::Deref;
use wit_bindgen_core::abi::LiftLower;
use wit_bindgen_core::{
    abi, uwrite, uwriteln, Direction, InterfaceGenerator as CoreInterfaceGenerator,
};
use wit_parser::abi::AbiVariant;
use wit_parser::{
    Docs, Enum, Flags, FlagsRepr, Function, FunctionKind, Handle, Int, InterfaceId, LiveTypes,
    Record, Resolve, Result_, Tuple, Type, TypeDefKind, TypeId, TypeOwner, Variant, WorldKey,
};

pub(crate) struct InterfaceFragment {
    pub(crate) csharp_src: String,
    pub(crate) csharp_interop_src: String,
    pub(crate) stub: String,
    pub(crate) usings: HashSet<String>,
    pub(crate) interop_usings: HashSet<String>,
}

pub(crate) struct InterfaceTypeAndFragments {
    pub(crate) is_export: bool,
    pub(crate) interface_fragments: Vec<InterfaceFragment>,
}

impl InterfaceTypeAndFragments {
    pub(crate) fn new(is_export: bool) -> Self {
        InterfaceTypeAndFragments {
            is_export,
            interface_fragments: Vec::<InterfaceFragment>::new(),
        }
    }
}

/// InterfaceGenerator generates the C# code for wit interfaces.
/// It produces types by interface in wit and then generates the interop code
/// by calling out to FunctionGenerator
pub(crate) struct InterfaceGenerator<'a> {
    pub(crate) src: String,
    pub(crate) csharp_interop_src: String,
    pub(crate) stub: String,
    pub(crate) csharp_gen: &'a mut CSharp,
    pub(crate) resolve: &'a Resolve,
    pub(crate) name: &'a str,
    pub(crate) direction: Direction,
    pub(crate) usings: HashSet<String>,
    pub(crate) interop_usings: HashSet<String>,
}

impl InterfaceGenerator<'_> {
    pub(crate) fn define_interface_types(&mut self, id: InterfaceId) {
        let mut live = LiveTypes::default();
        live.add_interface(self.resolve, id);
        self.define_live_types(live, id);
    }

    //TODO: we probably need this for anonymous types outside of an interface...
    // fn define_function_types(&mut self, funcs: &[(&str, &Function)]) {
    //     let mut live = LiveTypes::default();
    //     for (_, func) in funcs {
    //         live.add_func(self.resolve, func);
    //     }
    //     self.define_live_types(live);
    // }

    fn define_live_types(&mut self, live: LiveTypes, id: InterfaceId) {
        let mut type_names = HashMap::new();

        for ty in live.iter() {
            // just create c# types for wit anonymous types
            let type_def = &self.resolve.types[ty];
            if type_names.contains_key(&ty) || type_def.name.is_some() {
                continue;
            }

            let typedef_name = self.type_name(&Type::Id(ty));

            let prev = type_names.insert(ty, typedef_name.clone());
            assert!(prev.is_none());

            // workaround for owner not set on anonymous types, maintain or own map to the owner
            self.csharp_gen
                .anonymous_type_owners
                .insert(ty, TypeOwner::Interface(id));

            self.define_anonymous_type(ty, &typedef_name)
        }
    }

    fn define_anonymous_type(&mut self, type_id: TypeId, typedef_name: &str) {
        let type_def = &self.resolve().types[type_id];
        let kind = &type_def.kind;

        // TODO Does c# need this exit?
        // // skip `typedef handle_x handle_y` where `handle_x` is the same as `handle_y`
        // if let TypeDefKind::Handle(handle) = kind {
        //     let resource = match handle {
        //         Handle::Borrow(id) | Handle::Own(id) => id,
        //     };
        //     let origin = dealias(self.resolve, *resource);
        //     if origin == *resource {
        //         return;
        //     }
        // }

        //TODO: what other TypeDefKind do we need here?
        match kind {
            TypeDefKind::Tuple(t) => self.type_tuple(type_id, typedef_name, t, &type_def.docs),
            TypeDefKind::Option(t) => self.type_option(type_id, typedef_name, t, &type_def.docs),
            TypeDefKind::Record(t) => self.type_record(type_id, typedef_name, t, &type_def.docs),
            TypeDefKind::List(t) => self.type_list(type_id, typedef_name, t, &type_def.docs),
            TypeDefKind::Variant(t) => self.type_variant(type_id, typedef_name, t, &type_def.docs),
            TypeDefKind::Result(t) => self.type_result(type_id, typedef_name, t, &type_def.docs),
            TypeDefKind::Handle(_) => {
                // Handles don't require a separate definition beyond what we already define for the corresponding
                // resource types.
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn qualifier(&self, when: bool, ty: &TypeId) -> String {
        // anonymous types dont get an owner from wit-parser, so assume they are part of an interface here.
        let owner = if let Some(owner_type) = self.csharp_gen.anonymous_type_owners.get(ty) {
            *owner_type
        } else {
            let type_def = &self.resolve.types[*ty];
            type_def.owner
        };

        let global_prefix = self.global_if_user_type(&Type::Id(*ty));

        if let TypeOwner::Interface(id) = owner {
            if let Some(name) = self.csharp_gen.interface_names.get(&id) {
                if name != self.name {
                    return format!("{global_prefix}{name}.");
                }
            }
        }

        if when {
            let name = self.name;
            format!("{global_prefix}{name}.")
        } else {
            String::new()
        }
    }

    pub(crate) fn add_interface_fragment(self, is_export: bool) {
        self.csharp_gen
            .interface_fragments
            .entry(self.name.to_string())
            .or_insert_with(|| InterfaceTypeAndFragments::new(is_export))
            .interface_fragments
            .push(InterfaceFragment {
                csharp_src: self.src,
                csharp_interop_src: self.csharp_interop_src,
                stub: self.stub,
                usings: self.usings,
                interop_usings: self.interop_usings,
            });
    }

    pub(crate) fn add_world_fragment(self) {
        self.csharp_gen.world_fragments.push(InterfaceFragment {
            csharp_src: self.src,
            csharp_interop_src: self.csharp_interop_src,
            stub: self.stub,
            usings: self.usings,
            interop_usings: self.interop_usings,
        });
    }

    pub(crate) fn import(&mut self, import_module_name: &str, func: &Function) {
        let (camel_name, modifiers) = match &func.kind {
            FunctionKind::Freestanding | FunctionKind::Static(_) => {
                (func.item_name().to_upper_camel_case(), "static")
            }
            FunctionKind::Method(_) => (func.item_name().to_upper_camel_case(), ""),
            FunctionKind::Constructor(id) => (
                self.csharp_gen.all_resources[id].name.to_upper_camel_case(),
                "",
            ),
        };

        let access = self.csharp_gen.access_modifier();

        let extra_modifiers = extra_modifiers(func, &camel_name);

        let interop_camel_name = func.item_name().to_upper_camel_case();

        let sig = self.resolve.wasm_signature(AbiVariant::GuestImport, func);

        let wasm_result_type = match &sig.results[..] {
            [] => "void",
            [result] => crate::world_generator::wasm_type(*result),
            _ => unreachable!(),
        };

        let (result_type, results) = if let FunctionKind::Constructor(_) = &func.kind {
            (String::new(), Vec::new())
        } else {
            match func.results.len() {
                0 => ("void".to_string(), Vec::new()),
                1 => {
                    let (payload, results) = payload_and_results(
                        self.resolve,
                        *func.results.iter_types().next().unwrap(),
                        self.csharp_gen.opts.with_wit_results,
                    );
                    (
                        if let Some(ty) = payload {
                            self.csharp_gen.needs_result = true;
                            self.type_name_with_qualifier(&ty, true)
                        } else {
                            "void".to_string()
                        },
                        results,
                    )
                }
                _ => {
                    let types = func
                        .results
                        .iter_types()
                        .map(|ty| self.type_name_with_qualifier(ty, true))
                        .collect::<Vec<_>>()
                        .join(", ");
                    (format!("({})", types), Vec::new())
                }
            }
        };

        let wasm_params = sig
            .params
            .iter()
            .enumerate()
            .map(|(i, param)| {
                let ty = crate::world_generator::wasm_type(*param);
                format!("{ty} p{i}")
            })
            .collect::<Vec<_>>()
            .join(", ");

        let mut funcs: Vec<(String, String)> = Vec::new();
        funcs.push(self.gen_import_src(func, &results, ParameterType::ABI));

        let include_additional_functions = func
            .params
            .iter()
            .skip(if let FunctionKind::Method(_) = &func.kind {
                1
            } else {
                0
            })
            .any(|param| self.is_primative_list(&param.1));

        if include_additional_functions {
            funcs.push(self.gen_import_src(func, &results, ParameterType::Span));
            funcs.push(self.gen_import_src(func, &results, ParameterType::Memory));
        }

        let import_name = &func.name;

        self.csharp_gen
            .require_using("System.Runtime.InteropServices");

        let target = if let FunctionKind::Freestanding = &func.kind {
            self.require_interop_using("System.Runtime.InteropServices");
            &mut self.csharp_interop_src
        } else {
            self.require_using("System.Runtime.InteropServices");
            &mut self.src
        };

        uwrite!(
            target,
            r#"
            internal static class {interop_camel_name}WasmInterop
            {{
                [DllImport("{import_module_name}", EntryPoint = "{import_name}"), WasmImportLinkage]
                internal static extern {wasm_result_type} wasmImport{interop_camel_name}({wasm_params});
            }}
            "#
        );

        for (src, params) in funcs {
            uwrite!(
                target,
                r#"
                    {access} {extra_modifiers} {modifiers} unsafe {result_type} {camel_name}({params})
                    {{
                        {src}
                    }}
                "#
            );
        }
    }

    fn gen_import_src(
        &mut self,
        func: &Function,
        results: &Vec<TypeId>,
        parameter_type: ParameterType,
    ) -> (String, String) {
        let mut bindgen = FunctionBindgen::new(
            self,
            &func.item_name(),
            &func.kind,
            func.params
                .iter()
                .enumerate()
                .map(|(i, (name, _))| {
                    if i == 0 && matches!(&func.kind, FunctionKind::Method(_)) {
                        "this".to_owned()
                    } else {
                        name.to_csharp_ident()
                    }
                })
                .collect(),
            results.clone(),
            parameter_type,
        );

        abi::call(
            bindgen.interface_gen.resolve,
            AbiVariant::GuestImport,
            LiftLower::LowerArgsLiftResults,
            func,
            &mut bindgen,
            false,
        );

        let src = bindgen.src;

        let params = func
            .params
            .iter()
            .skip(if let FunctionKind::Method(_) = &func.kind {
                1
            } else {
                0
            })
            .map(|param| {
                let ty = self.name_with_qualifier(&param.1, true, parameter_type);
                let param_name = &param.0;
                let param_name = param_name.to_csharp_ident();
                format!("{ty} {param_name}")
            })
            .collect::<Vec<_>>()
            .join(", ");

        (src, params)
    }

    pub(crate) fn export(&mut self, func: &Function, interface_name: Option<&WorldKey>) {
        let (camel_name, modifiers) = match &func.kind {
            FunctionKind::Freestanding | FunctionKind::Static(_) => {
                (func.item_name().to_upper_camel_case(), "static abstract")
            }
            FunctionKind::Method(_) => (func.item_name().to_upper_camel_case(), ""),
            FunctionKind::Constructor(id) => (
                self.csharp_gen.all_resources[id].name.to_upper_camel_case(),
                "",
            ),
        };

        let extra_modifiers = extra_modifiers(func, &camel_name);

        let sig = self.resolve.wasm_signature(AbiVariant::GuestExport, func);

        let (result_type, results) = if let FunctionKind::Constructor(_) = &func.kind {
            (String::new(), Vec::new())
        } else {
            match func.results.len() {
                0 => ("void".to_owned(), Vec::new()),
                1 => {
                    let (payload, results) = payload_and_results(
                        self.resolve,
                        *func.results.iter_types().next().unwrap(),
                        self.csharp_gen.opts.with_wit_results,
                    );
                    (
                        if let Some(ty) = payload {
                            self.csharp_gen.needs_result = true;
                            self.type_name(&ty)
                        } else {
                            "void".to_string()
                        },
                        results,
                    )
                }
                _ => {
                    let types = func
                        .results
                        .iter_types()
                        .map(|ty| self.type_name(ty))
                        .collect::<Vec<String>>()
                        .join(", ");
                    (format!("({}) ", types), Vec::new())
                }
            }
        };

        let mut bindgen = FunctionBindgen::new(
            self,
            &func.item_name(),
            &func.kind,
            (0..sig.params.len()).map(|i| format!("p{i}")).collect(),
            results,
            ParameterType::ABI,
        );

        abi::call(
            bindgen.interface_gen.resolve,
            AbiVariant::GuestExport,
            LiftLower::LiftArgsLowerResults,
            func,
            &mut bindgen,
            false,
        );

        let src = bindgen.src;

        let vars = bindgen
            .resource_drops
            .iter()
            .map(|(t, v)| format!("{t}? {v} = null;"))
            .collect::<Vec<_>>()
            .join(";\n");

        let wasm_result_type = match &sig.results[..] {
            [] => "void",
            [result] => crate::world_generator::wasm_type(*result),
            _ => unreachable!(),
        };

        let wasm_params = sig
            .params
            .iter()
            .enumerate()
            .map(|(i, param)| {
                let ty = crate::world_generator::wasm_type(*param);
                format!("{ty} p{i}")
            })
            .collect::<Vec<_>>()
            .join(", ");

        let params = func
            .params
            .iter()
            .skip(if let FunctionKind::Method(_) = &func.kind {
                1
            } else {
                0
            })
            .map(|(name, ty)| {
                let ty = self.type_name(ty);
                let name = name.to_csharp_ident();
                format!("{ty} {name}")
            })
            .collect::<Vec<String>>()
            .join(", ");

        let interop_name = format!("wasmExport{}", func.name.to_upper_camel_case());
        let core_module_name = interface_name.map(|s| self.resolve.name_world_key(s));
        let export_name = func.legacy_core_export_name(core_module_name.as_deref());
        let access = self.csharp_gen.access_modifier();

        self.require_interop_using("System.Runtime.InteropServices");
        uwrite!(
            self.csharp_interop_src,
            r#"
            [UnmanagedCallersOnly(EntryPoint = "{export_name}")]
            {access} static unsafe {wasm_result_type} {interop_name}({wasm_params}) {{
                {vars}
                {src}
            }}
            "#
        );

        if !sig.results.is_empty() {
            uwrite!(
                self.csharp_interop_src,
                r#"
                [UnmanagedCallersOnly(EntryPoint = "cabi_post_{export_name}")]
                {access} static void cabi_post_{interop_name}({wasm_result_type} returnValue) {{
                    Console.WriteLine("TODO: cabi_post_{export_name}");
                }}
                "#
            );
        }

        if !matches!(&func.kind, FunctionKind::Constructor(_)) {
            uwrite!(
                self.src,
                r#"{extra_modifiers} {modifiers} {result_type} {camel_name}({params});

            "#
            );
        }

        if self.csharp_gen.opts.generate_stub {
            let sig = self.sig_string(func, true);

            uwrite!(
                self.stub,
                r#"
                {sig} {{
                    throw new NotImplementedException();
                }}
                "#
            );
        }
    }

    fn type_name(&mut self, ty: &Type) -> String {
        self.type_name_with_qualifier(ty, false)
    }

    // We use a global:: prefix to avoid conflicts with namespace clashes on partial namespace matches
    fn global_if_user_type(&self, ty: &Type) -> String {
        match ty {
            Type::Id(id) => {
                let ty = &self.resolve.types[*id];
                match &ty.kind {
                    TypeDefKind::Option(_ty) => "".to_owned(),
                    TypeDefKind::Result(_result) => "".to_owned(),
                    TypeDefKind::List(_list) => "".to_owned(),
                    TypeDefKind::Tuple(_tuple) => "".to_owned(),
                    TypeDefKind::Type(inner_type) => self.global_if_user_type(inner_type),
                    _ => "global::".to_owned(),
                }
            }
            _ => "".to_owned(),
        }
    }

    pub(crate) fn type_name_with_qualifier(&mut self, ty: &Type, qualifier: bool) -> String {
        self.name_with_qualifier(ty, qualifier, ParameterType::ABI)
    }

    fn is_primative_list(&mut self, ty: &Type) -> bool {
        match ty {
            Type::Id(id) => {
                let ty = &self.resolve.types[*id];
                match &ty.kind {
                    TypeDefKind::Type(ty) => self.is_primative_list(ty),
                    TypeDefKind::List(ty) if crate::world_generator::is_primitive(ty) => {
                        return true
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }

    pub(crate) fn name_with_qualifier(
        &mut self,
        ty: &Type,
        qualifier: bool,
        parameter_type: ParameterType,
    ) -> String {
        match ty {
            Type::Bool => "bool".to_owned(),
            Type::U8 => "byte".to_owned(),
            Type::U16 => "ushort".to_owned(),
            Type::U32 => "uint".to_owned(),
            Type::U64 => "ulong".to_owned(),
            Type::S8 => "sbyte".to_owned(),
            Type::S16 => "short".to_owned(),
            Type::S32 => "int".to_owned(),
            Type::S64 => "long".to_owned(),
            Type::F32 => "float".to_owned(),
            Type::F64 => "double".to_owned(),
            Type::Char => "uint".to_owned(),
            Type::String => "string".to_owned(),
            Type::Id(id) => {
                let ty = &self.resolve.types[*id];
                match &ty.kind {
                    TypeDefKind::Type(ty) => {
                        self.name_with_qualifier(ty, qualifier, parameter_type)
                    }
                    TypeDefKind::List(ty) => {
                        if crate::world_generator::is_primitive(ty)
                            && self.direction == Direction::Import
                            && parameter_type == ParameterType::Span
                        {
                            format!("Span<{}>", self.type_name(ty))
                        } else if crate::world_generator::is_primitive(ty)
                            && self.direction == Direction::Import
                            && parameter_type == ParameterType::Memory
                        {
                            format!("Memory<{}>", self.type_name(ty))
                        } else if crate::world_generator::is_primitive(ty) {
                            format!("{}[]", self.type_name(ty))
                        } else {
                            format!("List<{}>", self.type_name_with_qualifier(ty, qualifier))
                        }
                    }
                    TypeDefKind::Tuple(tuple) => {
                        let count = tuple.types.len();
                        self.csharp_gen.tuple_counts.insert(count);

                        let params = match count {
                            0 => String::new(),
                            1 => self
                                .type_name_with_qualifier(tuple.types.first().unwrap(), qualifier),
                            _ => format!(
                                "({})",
                                tuple
                                    .types
                                    .iter()
                                    .map(|ty| self.type_name_with_qualifier(ty, qualifier))
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            ),
                        };

                        params
                    }
                    TypeDefKind::Option(base_ty) => {
                        self.csharp_gen.needs_option = true;
                        let nesting = if let Type::Id(id) = base_ty {
                            matches!(&self.resolve.types[*id].kind, TypeDefKind::Option(_))
                        } else {
                            false
                        };
                        let base_ty = self.type_name_with_qualifier(base_ty, qualifier);
                        if nesting {
                            format!("Option<{base_ty}>")
                        } else {
                            format!("{base_ty}?")
                        }
                    }
                    TypeDefKind::Result(result) => {
                        self.csharp_gen.needs_result = true;
                        let mut name = |ty: &Option<Type>| {
                            ty.as_ref()
                                .map(|ty| self.type_name_with_qualifier(ty, qualifier))
                                .unwrap_or_else(|| "None".to_owned())
                        };
                        let ok = name(&result.ok);
                        let err = name(&result.err);

                        format!("Result<{ok}, {err}>")
                    }
                    TypeDefKind::Handle(handle) => {
                        let (Handle::Own(id) | Handle::Borrow(id)) = handle;
                        self.type_name_with_qualifier(&Type::Id(*id), qualifier)
                    }
                    _ => {
                        if let Some(name) = &ty.name {
                            format!(
                                "{}{}",
                                self.qualifier(qualifier, id),
                                name.to_upper_camel_case()
                            )
                        } else {
                            unreachable!("todo: {ty:?}")
                        }
                    }
                }
            }
        }
    }

    fn print_docs(&mut self, docs: &Docs) {
        if let Some(docs) = &docs.contents {
            let lines = docs
                .trim()
                .replace("<", "&lt;")
                .replace(">", "&gt;")
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

    pub(crate) fn non_empty_type<'a>(&self, ty: Option<&'a Type>) -> Option<&'a Type> {
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

    pub(crate) fn require_using(&mut self, using_ns: &str) {
        if !self.usings.contains(using_ns) {
            let using_ns_string = using_ns.to_string();
            self.usings.insert(using_ns_string);
        }
    }

    pub(crate) fn require_interop_using(&mut self, using_ns: &str) {
        if !self.interop_usings.contains(using_ns) {
            let using_ns_string = using_ns.to_string();
            self.interop_usings.insert(using_ns_string);
        }
    }

    pub(crate) fn start_resource(&mut self, id: TypeId, key: Option<&WorldKey>) {
        let access = self.csharp_gen.access_modifier();
        let qualified = self.type_name_with_qualifier(&Type::Id(id), true);
        let info = &self.csharp_gen.all_resources[&id];
        let name = info.name.clone();
        let upper_camel = name.to_upper_camel_case();
        let docs = info.docs.clone();
        self.print_docs(&docs);

        match self.direction {
            Direction::Import => {
                let module_name = key
                    .map(|key| self.resolve.name_world_key(key))
                    .unwrap_or_else(|| "$root".into());

                self.require_using("System.Runtime.InteropServices");
                // As of this writing, we cannot safely drop a handle to an imported resource from a .NET finalizer
                // because it may still have one or more open child resources.  Once WIT has explicit syntax for
                // indicating parent/child relationships, we should be able to use that information to keep track
                // of child resources automatically in generated code, at which point we'll be able to drop them in
                // the correct order from finalizers.
                uwriteln!(
                    self.src,
                    r#"
                    {access} class {upper_camel}: IDisposable {{
                        internal int Handle {{ get; set; }}

                        {access} readonly record struct THandle(int Handle);

                        {access} {upper_camel}(THandle handle) {{
                            Handle = handle.Handle;
                        }}

                        public void Dispose() {{
                            Dispose(true);
                        }}

                        [DllImport("{module_name}", EntryPoint = "[resource-drop]{name}"), WasmImportLinkage]
                        private static extern void wasmImportResourceDrop(int p0);

                        protected virtual void Dispose(bool disposing) {{
                            if (disposing && Handle != 0) {{
                                wasmImportResourceDrop(Handle);
                                Handle = 0;
                            }}
                        }}
                    "#
                );
            }
            Direction::Export => {
                let prefix = key
                    .map(|s| format!("{}#", self.resolve.name_world_key(s)))
                    .unwrap_or_else(String::new);

                self.require_interop_using("System.Runtime.InteropServices");
                uwrite!(
                    self.csharp_interop_src,
                    r#"
                    [UnmanagedCallersOnly(EntryPoint = "{prefix}[dtor]{name}")]
                    {access} static unsafe void wasmExportResourceDtor{upper_camel}(int rep) {{
                        var val = ({qualified}) {qualified}.repTable.Remove(rep);
                        val.Handle = 0;
                        // Note we call `Dispose` here even though the handle has already been disposed in case
                        // the implementation has overridden `Dispose(bool)`.
                        val.Dispose();
                    }}
                    "#
                );

                let module_name = key
                    .map(|key| format!("[export]{}", self.resolve.name_world_key(key)))
                    .unwrap_or_else(|| "[export]$root".into());

                self.require_using("System.Runtime.InteropServices");
                // The ergonomics of exported resources are not ideal, currently. Implementing such a resource
                // requires both extending a class and implementing an interface. The reason for the class is to
                // allow implementers to inherit code which tracks and disposes of the resource handle; the reason
                // for the interface is to express the API contract which the implementation must fulfill,
                // including static functions.
                //
                // We could remove the need for the class (and its `IDisposable` implementation) entirely if we
                // were to dispose of the handle immediately when lifting an owned handle, in which case we would
                // be left with nothing to keep track of or dispose later. However, we keep the handle alive in
                // case we want to give ownership back to the host again, in which case we'll be able to reuse the
                // same handle instead of calling `[resource-new]` to allocate a new one. Whether this optimization
                // is worth the trouble is open to debate, but we currently consider it a worthwhile tradeoff.
                //
                // Note that applications which export resources are relatively rare compared to those which only
                // import them, so in practice most developers won't encounter any of this anyway.
                uwriteln!(
                    self.src,
                    r#"
                    {access} abstract class {upper_camel}: IDisposable {{
                        internal static RepTable<{upper_camel}> repTable = new ();
                        internal int Handle {{ get; set; }}

                        public void Dispose() {{
                            Dispose(true);
                            GC.SuppressFinalize(this);
                        }}

                        internal static class WasmInterop {{
                            [DllImport("{module_name}", EntryPoint = "[resource-drop]{name}"), WasmImportLinkage]
                            internal static extern void wasmImportResourceDrop(int p0);

                            [DllImport("{module_name}", EntryPoint = "[resource-new]{name}"), WasmImportLinkage]
                            internal static extern int wasmImportResourceNew(int p0);

                            [DllImport("{module_name}", EntryPoint = "[resource-rep]{name}"), WasmImportLinkage]
                            internal static extern int wasmImportResourceRep(int p0);
                        }}

                        protected virtual void Dispose(bool disposing) {{
                            if (Handle != 0) {{
                                var handle = Handle;
                                Handle = 0;
                                WasmInterop.wasmImportResourceDrop(handle);
                            }}
                        }}

                        ~{upper_camel}() {{
                            Dispose(false);
                        }}
                    }}

                    {access} interface I{upper_camel} {{
                    "#
                );

                if self.csharp_gen.opts.generate_stub {
                    let super_ = self.type_name_with_qualifier(&Type::Id(id), true);
                    let interface = {
                        let split = super_.split('.').collect::<Vec<_>>();
                        split
                            .iter()
                            .map(|&v| v.to_owned())
                            .take(split.len() - 1)
                            .chain(split.last().map(|v| format!("I{v}")))
                            .collect::<Vec<_>>()
                            .join(".")
                    };

                    uwriteln!(
                        self.stub,
                        r#"
                        {access} class {upper_camel}: {super_}, {interface} {{
                        "#
                    );
                }
            }
        };
    }

    pub(crate) fn end_resource(&mut self) {
        if self.direction == Direction::Export && self.csharp_gen.opts.generate_stub {
            uwriteln!(
                self.stub,
                "
                }}
                "
            );
        }

        uwriteln!(
            self.src,
            "
            }}
            "
        );
    }

    fn sig_string(&mut self, func: &Function, qualifier: bool) -> String {
        let result_type = if let FunctionKind::Constructor(_) = &func.kind {
            String::new()
        } else {
            match func.results.len() {
                0 => "void".into(),
                1 => {
                    let (payload, _) = payload_and_results(
                        self.resolve,
                        *func.results.iter_types().next().unwrap(),
                        self.csharp_gen.opts.with_wit_results,
                    );
                    if let Some(ty) = payload {
                        self.csharp_gen.needs_result = true;
                        self.type_name_with_qualifier(&ty, qualifier)
                    } else {
                        "void".to_string()
                    }
                }
                count => {
                    self.csharp_gen.tuple_counts.insert(count);
                    format!(
                        "({})",
                        func.results
                            .iter_types()
                            .map(|ty| self.type_name_with_qualifier(ty, qualifier))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                }
            }
        };

        let params = func
            .params
            .iter()
            .skip(if let FunctionKind::Method(_) = &func.kind {
                1
            } else {
                0
            })
            .map(|(name, ty)| {
                let ty = self.type_name_with_qualifier(ty, qualifier);
                let name = name.to_csharp_ident();
                format!("{ty} {name}")
            })
            .collect::<Vec<_>>()
            .join(", ");

        let (camel_name, modifiers) = match &func.kind {
            FunctionKind::Freestanding | FunctionKind::Static(_) => {
                (func.item_name().to_upper_camel_case(), "static")
            }
            FunctionKind::Method(_) => (func.item_name().to_upper_camel_case(), ""),
            FunctionKind::Constructor(id) => (
                self.csharp_gen.all_resources[id].name.to_upper_camel_case(),
                "",
            ),
        };

        let access = self.csharp_gen.access_modifier();

        format!("{access} {modifiers} {result_type} {camel_name}({params})")
    }
}

impl<'a> CoreInterfaceGenerator<'a> for InterfaceGenerator<'a> {
    fn resolve(&self) -> &'a Resolve {
        self.resolve
    }

    fn type_record(&mut self, _id: TypeId, name: &str, record: &Record, docs: &Docs) {
        let access = self.csharp_gen.access_modifier();

        self.print_docs(docs);

        let name = name.to_upper_camel_case();

        let parameters = record
            .fields
            .iter()
            .map(|field| {
                format!(
                    "{} {}",
                    self.type_name(&field.ty),
                    field.name.to_csharp_ident()
                )
            })
            .collect::<Vec<_>>()
            .join(", ");

        let assignments = record
            .fields
            .iter()
            .map(|field| {
                let name = field.name.to_csharp_ident();
                format!("this.{name} = {name};")
            })
            .collect::<Vec<_>>()
            .join("\n");

        let fields = if record.fields.is_empty() {
            format!("{access} const {name} INSTANCE = new {name}();")
        } else {
            record
                .fields
                .iter()
                .map(|field| {
                    format!(
                        "{access} readonly {} {};",
                        self.type_name(&field.ty),
                        field.name.to_csharp_ident()
                    )
                })
                .collect::<Vec<_>>()
                .join("\n")
        };

        uwrite!(
            self.src,
            "
            {access} class {name} {{
                {fields}

                {access} {name}({parameters}) {{
                    {assignments}
                }}
            }}
            "
        );
    }

    fn type_flags(&mut self, _id: TypeId, name: &str, flags: &Flags, docs: &Docs) {
        self.print_docs(docs);

        let name = name.to_upper_camel_case();

        let enum_elements = flags
            .flags
            .iter()
            .enumerate()
            .map(|(i, flag)| {
                let flag_name = flag.name.to_shouty_snake_case();
                let suffix = if matches!(flags.repr(), FlagsRepr::U32(2)) {
                    "UL"
                } else {
                    ""
                };
                format!("{flag_name} = 1{suffix} << {i},")
            })
            .collect::<Vec<_>>()
            .join("\n");

        let enum_type = match flags.repr() {
            FlagsRepr::U32(2) => ": ulong",
            FlagsRepr::U16 => ": ushort",
            FlagsRepr::U8 => ": byte",
            _ => "",
        };

        let access = self.csharp_gen.access_modifier();

        uwrite!(
            self.src,
            "
            {access} enum {name} {enum_type} {{
                {enum_elements}
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
        let access = self.csharp_gen.access_modifier();

        let constructors = variant
            .cases
            .iter()
            .map(|case| {
                let case_name = case.name.to_csharp_ident();
                let tag = case.name.to_csharp_ident_upper();
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
                    "{access} static {name} {tag}({parameter}) {{
                         return new {name}(Tags.{tag}, {argument});
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
                    let tag = case.name.to_csharp_ident_upper();
                    let ty = self.type_name(ty);
                    format!(
                        r#"{access} {ty} As{case_name}
                        {{
                            get
                            {{
                                if (Tag == Tags.{tag})
                                    return ({ty})value!;
                                else
                                    throw new ArgumentException("expected {tag}, got " + Tag);
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
                let tag = case.name.to_csharp_ident_upper();
                format!("{access} const {tag_type} {tag} = {i};")
            })
            .collect::<Vec<_>>()
            .join("\n");

        uwrite!(
            self.src,
            "
            {access} class {name} {{
                {access} readonly {tag_type} Tag;
                private readonly object? value;

                private {name}({tag_type} tag, object? value) {{
                    this.Tag = tag;
                    this.value = value;
                }}

                {constructors}
                {accessors}

                {access} class Tags {{
                    {tags}
                }}
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

        let access = self.csharp_gen.access_modifier();

        uwrite!(
            self.src,
            "
            {access} enum {name} {{
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

    fn type_builtin(&mut self, _id: TypeId, _name: &str, _ty: &Type, _docs: &Docs) {
        unimplemented!();
    }

    fn type_resource(&mut self, id: TypeId, name: &str, docs: &Docs) {
        // Here we just record information about the resource; we don't actually emit any code until we're ready to
        // visit any functions associated with the resource (e.g. in CSharp::import_interface, etc.).
        self.csharp_gen
            .all_resources
            .entry(id)
            .or_insert_with(|| ResourceInfo {
                module: self.name.to_owned(),
                name: name.to_owned(),
                docs: docs.clone(),
                direction: Direction::Import,
            })
            .direction = self.direction;
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
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub(crate) enum ParameterType {
    ABI,
    Span,
    Memory,
}

fn payload_and_results(
    resolve: &Resolve,
    ty: Type,
    with_wit_results: bool,
) -> (Option<Type>, Vec<TypeId>) {
    if with_wit_results {
        return (Some(ty), Vec::new());
    }

    fn recurse(resolve: &Resolve, ty: Type, results: &mut Vec<TypeId>) -> Option<Type> {
        if let Type::Id(id) = ty {
            if let TypeDefKind::Result(result) = &resolve.types[id].kind {
                results.push(id);
                if let Some(ty) = result.ok {
                    recurse(resolve, ty, results)
                } else {
                    None
                }
            } else {
                Some(ty)
            }
        } else {
            Some(ty)
        }
    }

    let mut results = Vec::new();
    let payload = recurse(resolve, ty, &mut results);
    (payload, results)
}

fn extra_modifiers(func: &Function, name: &str) -> &'static str {
    if let FunctionKind::Method(_) = &func.kind {
        // Avoid warnings about name clashes.
        //
        // TODO: add other `object` method names here
        if name == "GetType" {
            return "new";
        }
    }

    ""
}

fn int_type(int: Int) -> &'static str {
    match int {
        Int::U8 => "byte",
        Int::U16 => "ushort",
        Int::U32 => "uint",
        Int::U64 => "ulong",
    }
}
