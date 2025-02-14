use anyhow::Result;
use core::panic;
use heck::{ToLowerCamelCase, ToShoutySnakeCase, ToSnakeCase, ToUpperCamelCase};
use std::{collections::HashMap, fmt::Write, mem, ops::Deref};
use wit_bindgen_core::{
    abi::{self, AbiVariant, Bindgen, Bitcast, Instruction, LiftLower, WasmType},
    dealias, uwrite, uwriteln,
    wit_parser::{
        Alignment, ArchitectureSize, Docs, Enum, Flags, FlagsRepr, Function, FunctionKind, Handle,
        Int, InterfaceId, Record, Resolve, Result_, SizeAlign, Tuple, Type, TypeDef, TypeDefKind,
        TypeId, TypeOwner, Variant, WorldId, WorldKey,
    },
    Direction, Files, InterfaceGenerator as _, Ns, Source, WorldGenerator,
};

// Assumptions:
// - Data: u8 -> Byte, s8 | s16 | s32 -> Int, u16 | u32 -> UInt, s64 -> Int64, u64 -> UInt64, f32 | f64 -> Double, address -> Int
// - Encoding: UTF16
// - Lift/Lower list<T>: T == Int/UInt/Int64/UInt64/Float/Double -> FixedArray[T], T == Byte -> Bytes, T == Char -> String
// Organization:
// - one package per interface (export and import are treated as different interfaces)
// - ffi utils are under `./ffi`, and the project entrance (package as link target) is under `./gen`
// TODO: Export will share the type signatures with the import by using a newtype alias

const FFI_DIR: &str = "ffi";

const FFI: &str = r#"
pub extern "wasm" fn extend16(value : Int) -> Int =
  #|(func (param i32) (result i32) local.get 0 i32.extend16_s)

pub extern "wasm" fn extend8(value : Int) -> Int =
  #|(func (param i32) (result i32) local.get 0 i32.extend8_s)

pub extern "wasm" fn store8(offset : Int, value : Int) =
  #|(func (param i32) (param i32) local.get 0 local.get 1 i32.store8)

pub extern "wasm" fn load8_u(offset : Int) -> Int =
  #|(func (param i32) (result i32) local.get 0 i32.load8_u)

pub extern "wasm" fn load8(offset : Int) -> Int =
  #|(func (param i32) (result i32) local.get 0 i32.load8_s)

pub extern "wasm" fn store16(offset : Int, value : Int) =
  #|(func (param i32) (param i32) local.get 0 local.get 1 i32.store16)

pub extern "wasm" fn load16(offset : Int) -> Int =
  #|(func (param i32) (result i32) local.get 0 i32.load16_s)

pub extern "wasm" fn load16_u(offset : Int) -> Int =
  #|(func (param i32) (result i32) local.get 0 i32.load16_u)

pub extern "wasm" fn store32(offset : Int, value : Int) =
  #|(func (param i32) (param i32) local.get 0 local.get 1 i32.store)

pub extern "wasm" fn load32(offset : Int) -> Int =
  #|(func (param i32) (result i32) local.get 0 i32.load)

pub extern "wasm" fn store64(offset : Int, value : Int64) =
  #|(func (param i32) (param i64) local.get 0 local.get 1 i64.store)

pub extern "wasm" fn load64(offset : Int) -> Int64 =
  #|(func (param i32) (result i64) local.get 0 i64.load)

pub extern "wasm" fn storef32(offset : Int, value : Float) =
  #|(func (param i32) (param f32) local.get 0 local.get 1 f32.store)

pub extern "wasm" fn loadf32(offset : Int) -> Float =
  #|(func (param i32) (result f32) local.get 0 f32.load)

pub extern "wasm" fn storef64(offset : Int, value : Double) =
  #|(func (param i32) (param f64) local.get 0 local.get 1 f64.store)

pub extern "wasm" fn loadf64(offset : Int) -> Double =
  #|(func (param i32) (result f64) local.get 0 f64.load)

pub extern "wasm" fn f32_to_i32(value : Float) -> Int =
  #|(func (param f32) (result i32) local.get 0 f32.convert_i32_s)

pub extern "wasm" fn f32_to_i64(value : Float) -> Int64 =
  #|(func (param f32) (result i64) local.get 0 f32.convert_i64_s)

extern "wasm" fn malloc_inline(size : Int) -> Int =
  #|(func (param i32) (result i32) local.get 0 call $moonbit.malloc)

pub fn malloc(size : Int) -> Int {
  let words = size / 4 + 1
  let address = malloc_inline(8 + words * 4)
  store32(address, 1)
  store32(address + 4, (words << 8) | 246)
  store8(address + words * 4 + 7, 3 - size % 4)
  address + 8
}

pub extern "wasm" fn free(position : Int) =
  #|(func (param i32) local.get 0 i32.const 8 i32.sub call $moonbit.decref)

pub fn copy(dest : Int, src : Int) -> Unit {
  let src_len = (load32(src - 12) >> 2) - 4
  let dest_len = (load32(dest - 12) >> 2) - 4
  let min = if src_len < dest_len { src_len } else { dest_len }
  copy_inline(dest, src, min)
}

extern "wasm" fn copy_inline(dest : Int, src : Int, len : Int) =
  #|(func (param i32) (param i32) (param i32) local.get 0 local.get 1 local.get 2 memory.copy)

pub extern "wasm" fn str2ptr(str : String) -> Int =
  #|(func (param i32) (result i32) local.get 0 i32.const 8 i32.add)

pub extern "wasm" fn ptr2str(ptr : Int) -> String =
  #|(func (param i32) (result i32) local.get 0 i32.const 4 i32.sub i32.const 243 i32.store8 local.get 0 i32.const 8 i32.sub)

pub extern "wasm" fn bytes2ptr(bytes : FixedArray[Byte]) -> Int =
  #|(func (param i32) (result i32) local.get 0 i32.const 8 i32.add)

pub extern "wasm" fn ptr2bytes(ptr : Int, _len : Int) -> FixedArray[Byte] =
  #|(func (param i32) (param i32) (result i32) local.get 0 i32.const 8 i32.sub)

pub extern "wasm" fn uint_array2ptr(array : FixedArray[UInt]) -> Int =
  #|(func (param i32) (result i32) local.get 0 i32.const 8 i32.add)

pub extern "wasm" fn uint64_array2ptr(array : FixedArray[UInt64]) -> Int =
  #|(func (param i32) (result i32) local.get 0 i32.const 8 i32.add)

pub extern "wasm" fn int_array2ptr(array : FixedArray[Int]) -> Int =
  #|(func (param i32) (result i32) local.get 0 i32.const 8 i32.add)

pub extern "wasm" fn int64_array2ptr(array : FixedArray[Int64]) -> Int =
  #|(func (param i32) (result i32) local.get 0 i32.const 8 i32.add)

pub extern "wasm" fn float_array2ptr(array : FixedArray[Float]) -> Int =
  #|(func (param i32) (result i32) local.get 0 i32.const 8 i32.add)

pub extern "wasm" fn double_array2ptr(array : FixedArray[Double]) -> Int =
  #|(func (param i32) (result i32) local.get 0 i32.const 8 i32.add)

extern "wasm" fn ptr2uint_array_ffi(ptr : Int) -> FixedArray[UInt] =
  #|(func (param i32) (result i32) local.get 0 i32.const 8 i32.sub)

pub fn ptr2uint_array(ptr : Int, len : Int) -> FixedArray[UInt] {
  set_header_ffi(ptr - 4, len)
  ptr2uint_array_ffi(ptr)
}

extern "wasm" fn ptr2int_array_ffi(ptr : Int) -> FixedArray[Int] =
  #|(func (param i32) (result i32) local.get 0 i32.const 8 i32.sub)

pub fn ptr2int_array(ptr : Int, len : Int) -> FixedArray[Int] {
  set_header_ffi(ptr - 4, len)
  ptr2int_array_ffi(ptr)
}

extern "wasm" fn ptr2float_array_ffi(ptr : Int) -> FixedArray[Float] =
  #|(func (param i32) (result i32) local.get 0 i32.const 8 i32.sub)

pub fn ptr2float_array(ptr : Int, len : Int) -> FixedArray[Float] {
  set_header_ffi(ptr - 4, len)
  ptr2float_array_ffi(ptr)
}
extern "wasm" fn ptr2uint64_array_ffi(ptr : Int) -> FixedArray[UInt64] =
  #|(func (param i32) (result i32) local.get 0 i32.const 8 i32.sub)

pub fn ptr2uint64_array(ptr : Int, len : Int) -> FixedArray[UInt64] {
  set_header_ffi(ptr - 4, len)
  ptr2uint64_array_ffi(ptr)
}

extern "wasm" fn ptr2int64_array_ffi(ptr : Int) -> FixedArray[Int64] =
  #|(func (param i32) (result i32) local.get 0 i32.const 8 i32.sub)

pub fn ptr2int64_array(ptr : Int, len : Int) -> FixedArray[Int64] {
  set_header_ffi(ptr - 4, len)
  ptr2int64_array_ffi(ptr)
}

extern "wasm" fn ptr2double_array_ffi(ptr : Int) -> FixedArray[Double] =
  #|(func (param i32) (result i32) local.get 0 i32.const 8 i32.sub)

pub fn ptr2double_array(ptr : Int, len : Int) -> FixedArray[Double] {
  set_header_ffi(ptr - 4, len)
  ptr2double_array_ffi(ptr)
}

fn set_header_ffi(offset : Int, len : Int) -> Unit {
  store32(offset, len << 8 | 241)
}

pub fn cabi_realloc(
    src_offset : Int,
    src_size : Int,
    _dst_alignment : Int,
    dst_size : Int
) -> Int {{
    // malloc
    if src_offset == 0 && src_size == 0 {{
        return malloc(dst_size)
    }}
    // free
    if dst_size <= 0 {{
        free(src_offset)
        return 0
    }}
    // realloc
    let dst = malloc(dst_size)
    copy(dst, src_offset)
    free(src_offset)
    dst
}}  

pub(open) trait Any {}
pub(all) struct Cleanup {
    address : Int
    size : Int
    align : Int
}
"#;

#[derive(Default, Debug, Clone)]
#[cfg_attr(feature = "clap", derive(clap::Args))]
pub struct Opts {
    /// Whether or not to derive Show for all types
    #[cfg_attr(feature = "clap", arg(long, default_value_t = false))]
    pub derive_show: bool,
    /// Whether or not to derive Eq for all types
    #[cfg_attr(feature = "clap", arg(long, default_value_t = false))]
    pub derive_eq: bool,
    /// Whether or not to declare as Error type for types ".*error"
    #[cfg_attr(feature = "clap", arg(long, default_value_t = false))]
    pub derive_error: bool,
    /// Whether or not to generate stub files ; useful for update after WIT change
    #[cfg_attr(feature = "clap", arg(long, default_value_t = false))]
    pub ignore_stub: bool,
    /// Whether or not to generate moon.mod.json ; useful if the project is part of a larger project
    #[cfg_attr(feature = "clap", arg(long, default_value_t = false))]
    pub ignore_module_file: bool,
    /// The package/dir to generate the program entrance
    #[cfg_attr(feature = "clap", arg(long, default_value = "gen"))]
    pub gen_dir: String,
    /// The project name ; or the package path prefix if the project is part of a larger project
    #[cfg_attr(feature = "clap", arg(long, default_value = None))]
    pub project_name: Option<String>,
}

impl Opts {
    pub fn build(&self) -> Box<dyn WorldGenerator> {
        Box::new(MoonBit {
            opts: self.clone(),
            ..MoonBit::default()
        })
    }
}

struct InterfaceFragment {
    src: String,
    ffi: String,
    stub: String,
}

#[derive(Default)]
struct Imports {
    packages: HashMap<String, String>,
    ns: Ns,
}

#[derive(Default)]
pub struct MoonBit {
    opts: Opts,
    name: String,
    needs_cleanup: bool,
    import_interface_fragments: HashMap<String, Vec<InterfaceFragment>>,
    export_interface_fragments: HashMap<String, Vec<InterfaceFragment>>,
    import_world_fragments: Vec<InterfaceFragment>,
    export_world_fragments: Vec<InterfaceFragment>,
    sizes: SizeAlign,
    import_interface_names: HashMap<InterfaceId, String>,
    export_interface_names: HashMap<InterfaceId, String>,
    interface_ns: Ns,
    // dependencies between packages
    package_import: HashMap<String, Imports>,
    export: HashMap<String, String>,
    export_ns: Ns,
    // return area allocation
    return_area_size: ArchitectureSize,
    return_area_align: Alignment,
}

impl MoonBit {
    fn interface<'a>(
        &'a mut self,
        resolve: &'a Resolve,
        name: &'a str,
        module: &'a str,
        direction: Direction,
    ) -> InterfaceGenerator<'a> {
        InterfaceGenerator {
            src: String::new(),
            stub: String::new(),
            ffi: String::new(),
            gen: self,
            resolve,
            name,
            module,
            direction,
        }
    }
}

impl WorldGenerator for MoonBit {
    fn preprocess(&mut self, resolve: &Resolve, world: WorldId) {
        self.name = world_name(resolve, world);
        self.sizes.fill(resolve);
    }

    fn import_interface(
        &mut self,
        resolve: &Resolve,
        key: &WorldKey,
        id: InterfaceId,
        files: &mut Files,
    ) -> Result<()> {
        let name = interface_name(resolve, key);
        let name = self.interface_ns.tmp(&name);
        self.import_interface_names.insert(id, name.clone());

        if let Some(content) = &resolve.interfaces[id].docs.contents {
            if !content.is_empty() {
                files.push(
                    &format!("{}/README.md", name.replace(".", "/")),
                    content.as_bytes(),
                );
            }
        }

        let module = &resolve.name_world_key(key);
        let mut gen = self.interface(resolve, &name, module, Direction::Import);
        gen.types(id);

        for (_, func) in resolve.interfaces[id].functions.iter() {
            gen.import(module, func);
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
        let mut gen = self.interface(resolve, &name, "$root", Direction::Import);

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
        files: &mut Files,
    ) -> Result<()> {
        let name = format!("{}.{}", self.opts.gen_dir, interface_name(resolve, key));
        let name = self.interface_ns.tmp(&name);
        self.export_interface_names.insert(id, name.clone());

        if let Some(content) = &resolve.interfaces[id].docs.contents {
            if !content.is_empty() {
                files.push(
                    &format!("{}/README.md", name.replace(".", "/")),
                    content.as_bytes(),
                );
            }
        }

        let module = &resolve.name_world_key(key);
        let mut gen = self.interface(resolve, &name, module, Direction::Export);
        gen.types(id);

        for (_, func) in resolve.interfaces[id].functions.iter() {
            gen.export(Some(module), func);
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
        let name = format!("{}.{}", self.opts.gen_dir, world_name(resolve, world));
        let mut gen = self.interface(resolve, &name, "$root", Direction::Export);

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
        let mut gen = self.interface(resolve, &name, "$root", Direction::Import);

        for (ty_name, ty) in types {
            gen.define_type(ty_name, *ty);
        }

        gen.add_world_fragment();
    }

    fn finish(&mut self, resolve: &Resolve, id: WorldId, files: &mut Files) -> Result<()> {
        let project_name = self
            .opts
            .project_name
            .clone()
            .or(resolve.worlds[id].package.map(|id| {
                let package = &resolve.packages[id].name;
                format!("{}/{}", package.namespace, package.name)
            }))
            .unwrap_or("generated".into());
        let name = world_name(resolve, id);

        if let Some(content) = &resolve.worlds[id].docs.contents {
            if !content.is_empty() {
                files.push(
                    &format!("{}/README.md", name.replace(".", "/")),
                    content.as_bytes(),
                );
            }
        }

        let version = env!("CARGO_PKG_VERSION");

        let generate_pkg_definition = |name: &String, files: &mut Files| {
            let directory = name.replace('.', "/");
            let imports: Option<&Imports> = self.package_import.get(name);
            if let Some(imports) = imports {
                let mut deps = imports
                    .packages
                    .iter()
                    .map(|(k, v)| {
                        format!(
                            "{{ \"path\" : \"{project_name}/{}\", \"alias\" : \"{}\" }}",
                            k.replace(".", "/"),
                            v
                        )
                    })
                    .collect::<Vec<_>>();
                deps.sort();

                files.push(
                    &format!("{directory}/moon.pkg.json"),
                    format!("{{ \"import\": [{}] }}", deps.join(", ")).as_bytes(),
                );
            } else {
                files.push(
                    &format!("{directory}/moon.pkg.json"),
                    format!("{{ }}").as_bytes(),
                );
            }
        };

        // Import world fragments
        let mut src = Source::default();
        let mut ffi = Source::default();
        wit_bindgen_core::generated_preamble(&mut src, version);
        wit_bindgen_core::generated_preamble(&mut ffi, version);
        self.import_world_fragments.iter().for_each(|f| {
            uwriteln!(src, "{}", f.src);
            uwriteln!(ffi, "{}", f.ffi);
            assert!(f.stub.is_empty());
        });

        let directory = name.replace('.', "/");
        files.push(&format!("{directory}/import.mbt"), indent(&src).as_bytes());
        files.push(
            &format!("{directory}/ffi_import.mbt"),
            indent(&ffi).as_bytes(),
        );
        generate_pkg_definition(&name, files);

        // Export world fragments
        let mut src = Source::default();
        let mut stub = Source::default();
        wit_bindgen_core::generated_preamble(&mut src, version);
        generated_preamble(&mut stub, version);
        self.export_world_fragments.iter().for_each(|f| {
            uwriteln!(src, "{}", f.src);
            uwriteln!(stub, "{}", f.stub);
        });

        files.push(&format!("{directory}/top.mbt"), indent(&src).as_bytes());
        if !self.opts.ignore_stub {
            files.push(
                &format!("{}/{directory}/stub.mbt", self.opts.gen_dir),
                indent(&stub).as_bytes(),
            );
            generate_pkg_definition(&format!("{}.{}", self.opts.gen_dir, name), files);
        }

        let generate_ffi =
            |directory: String, fragments: &[InterfaceFragment], files: &mut Files| {
                let b = fragments
                    .iter()
                    .map(|f| f.ffi.deref())
                    .collect::<Vec<_>>()
                    .join("\n");

                let mut body = Source::default();
                wit_bindgen_core::generated_preamble(&mut body, version);
                uwriteln!(&mut body, "{b}");

                files.push(
                    &format!(
                        "{}/{}_export.mbt",
                        self.opts.gen_dir,
                        directory.to_snake_case()
                    ),
                    indent(&body).as_bytes(),
                );
            };

        generate_ffi(directory, &self.export_world_fragments, files);

        // Import interface fragments
        for (name, fragments) in &self.import_interface_fragments {
            let mut src = Source::default();
            let mut ffi = Source::default();
            wit_bindgen_core::generated_preamble(&mut src, version);
            wit_bindgen_core::generated_preamble(&mut ffi, version);
            fragments.iter().for_each(|f| {
                uwriteln!(src, "{}", f.src);
                uwriteln!(ffi, "{}", f.ffi);
                assert!(f.stub.is_empty());
            });

            let directory = name.replace('.', "/");
            files.push(&format!("{directory}/top.mbt"), indent(&src).as_bytes());
            files.push(&format!("{directory}/ffi.mbt"), indent(&ffi).as_bytes());
            generate_pkg_definition(&name, files);
        }

        // Export interface fragments
        for (name, fragments) in &self.export_interface_fragments {
            let mut src = Source::default();
            let mut stub = Source::default();
            wit_bindgen_core::generated_preamble(&mut src, version);
            generated_preamble(&mut stub, version);
            fragments.iter().for_each(|f| {
                uwriteln!(src, "{}", f.src);
                uwriteln!(stub, "{}", f.stub);
            });

            let directory = name.replace('.', "/");
            files.push(&format!("{directory}/top.mbt"), indent(&src).as_bytes());
            if !self.opts.ignore_stub {
                files.push(&format!("{directory}/stub.mbt"), indent(&stub).as_bytes());
                generate_pkg_definition(&name, files);
            }
            generate_ffi(directory, fragments, files);
        }

        // Export FFI Utils
        let mut body = Source::default();
        wit_bindgen_core::generated_preamble(&mut body, version);
        body.push_str(FFI);
        files.push(&format!("{FFI_DIR}/top.mbt"), indent(&body).as_bytes());
        files.push(&format!("{FFI_DIR}/moon.pkg.json"), "{}".as_bytes());

        // Export project files
        if !self.opts.ignore_stub && !self.opts.ignore_module_file {
            let mut body = Source::default();
            uwriteln!(&mut body, "{{ \"name\": \"{project_name}\" }}");
            files.push(&format!("moon.mod.json"), body.as_bytes());
        }

        let export_dir = self.opts.gen_dir.clone();

        // Export project entry point
        let mut gen = self.interface(resolve, &export_dir.as_str(), "", Direction::Export);
        let ffi_qualifier = gen.qualify_package(FFI_DIR);

        let mut body = Source::default();
        wit_bindgen_core::generated_preamble(&mut body, version);
        uwriteln!(
            &mut body,
            "
            pub fn cabi_realloc(
                src_offset : Int,
                src_size : Int,
                dst_alignment : Int,
                dst_size : Int
            ) -> Int {{
                {ffi_qualifier}cabi_realloc(src_offset, src_size, dst_alignment, dst_size)
            }}
            "
        );
        if !self.return_area_size.is_empty() {
            uwriteln!(
                &mut body,
                "
                let return_area : Int = {ffi_qualifier}malloc({})
                ",
                self.return_area_size.size_wasm32(),
            );
        }
        files.push(
            &format!("{}/ffi.mbt", self.opts.gen_dir),
            indent(&body).as_bytes(),
        );
        self.export
            .insert("cabi_realloc".into(), "cabi_realloc".into());

        let mut body = Source::default();
        let mut exports = self
            .export
            .iter()
            .map(|(k, v)| format!("\"{k}:{v}\""))
            .collect::<Vec<_>>();
        exports.sort();

        uwrite!(
            &mut body,
            r#"
            {{
                "link": {{
                    "wasm": {{
                        "exports": [{}],
                        "export-memory-name": "memory",
                        "heap-start-address": 16
                    }}
                }}
            "#,
            exports.join(", ")
        );
        if let Some(imports) = self.package_import.get(&self.opts.gen_dir) {
            let mut deps = imports
                .packages
                .iter()
                .map(|(k, v)| {
                    format!(
                        "{{ \"path\" : \"{project_name}/{}\", \"alias\" : \"{}\" }}",
                        k.replace(".", "/"),
                        v
                    )
                })
                .collect::<Vec<_>>();
            deps.sort();

            uwrite!(&mut body, "    ,\"import\": [{}]", deps.join(", "));
        }
        uwrite!(
            &mut body,
            "
            }}
            ",
        );
        files.push(
            &format!("{}/moon.pkg.json", self.opts.gen_dir,),
            indent(&body).as_bytes(),
        );

        Ok(())
    }
}

struct InterfaceGenerator<'a> {
    src: String,
    stub: String,
    ffi: String,
    gen: &'a mut MoonBit,
    resolve: &'a Resolve,
    // The current interface getting generated
    name: &'a str,
    module: &'a str,
    direction: Direction,
}

impl InterfaceGenerator<'_> {
    fn qualify_package(&mut self, name: &str) -> String {
        if name != self.name {
            let imports = self
                .gen
                .package_import
                .entry(
                    // This is a hack: the exported ffi calls are actually under the gen directory
                    if self.direction == Direction::Export && name == FFI_DIR {
                        self.gen.opts.gen_dir.clone()
                    } else {
                        self.name.to_string()
                    },
                )
                .or_default();
            if let Some(alias) = imports.packages.get(name) {
                return format!("@{}.", alias);
            } else {
                let alias = imports
                    .ns
                    .tmp(&name.split(".").last().unwrap().to_lower_camel_case());
                imports
                    .packages
                    .entry(name.to_string())
                    .or_insert(alias.clone());
                return format!("@{}.", alias);
            }
        } else {
            "".into()
        }
    }
    fn qualifier(&mut self, ty: &TypeDef) -> String {
        if let TypeOwner::Interface(id) = &ty.owner {
            if let Some(name) = self.gen.export_interface_names.get(id) {
                if name != self.name {
                    return self.qualify_package(&name.clone());
                }
            } else if let Some(name) = self.gen.import_interface_names.get(id) {
                if name != self.name {
                    return self.qualify_package(&name.clone());
                }
            }
        } else if let TypeOwner::World(id) = &ty.owner {
            let name = world_name(self.resolve, *id);
            if name != self.name {
                return self.qualify_package(&name.clone());
            }
        }

        String::new()
    }

    fn add_interface_fragment(self) {
        match self.direction {
            Direction::Import => {
                self.gen
                    .import_interface_fragments
                    .entry(self.name.to_owned())
                    .or_default()
                    .push(InterfaceFragment {
                        src: self.src,
                        stub: self.stub,
                        ffi: self.ffi,
                    });
            }
            Direction::Export => {
                self.gen
                    .export_interface_fragments
                    .entry(self.name.to_owned())
                    .or_default()
                    .push(InterfaceFragment {
                        src: self.src,
                        stub: self.stub,
                        ffi: self.ffi,
                    });
            }
        }
    }

    fn add_world_fragment(self) {
        match self.direction {
            Direction::Import => {
                self.gen.import_world_fragments.push(InterfaceFragment {
                    src: self.src,
                    stub: self.stub,
                    ffi: self.ffi,
                });
            }
            Direction::Export => {
                self.gen.export_world_fragments.push(InterfaceFragment {
                    src: self.src,
                    stub: self.stub,
                    ffi: self.ffi,
                });
            }
        }
    }

    fn import(&mut self, module: &str, func: &Function) {
        let mut bindgen = FunctionBindgen::new(
            self,
            &func.name,
            self.name,
            func.params
                .iter()
                .map(|(name, _)| name.to_moonbit_ident())
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

            let ffi_qualifier = self.qualify_package(FFI_DIR);

            format!(
                r#"let cleanupList : Array[{ffi_qualifier}Cleanup] = []
                   let ignoreList : Array[&{ffi_qualifier}Any] = []"#
            )
        } else {
            String::new()
        };

        let name = &func.name;

        let sig = self.resolve.wasm_signature(AbiVariant::GuestImport, func);

        let result_type = match &sig.results[..] {
            [] => "".into(),
            [result] => format!("-> {}", wasm_type(*result)),
            _ => unreachable!(),
        };

        let camel_name = func.name.to_upper_camel_case();

        let params = sig
            .params
            .iter()
            .enumerate()
            .map(|(i, param)| {
                let ty = wasm_type(*param);
                format!("p{i} : {ty}")
            })
            .collect::<Vec<_>>()
            .join(", ");

        let sig = self.sig_string(func, false);

        uwriteln!(
            self.ffi,
            r#"fn wasmImport{camel_name}({params}) {result_type} = "{module}" "{name}""#
        );

        print_docs(&mut self.src, &func.docs);

        uwrite!(
            self.src,
            r#"
            {sig} {{
              {cleanup_list}
              {src}
            }}
            "#
        );
    }

    fn export(&mut self, interface_name: Option<&str>, func: &Function) {
        let sig = self.resolve.wasm_signature(AbiVariant::GuestExport, func);

        let func_sig = self.sig_string(func, true);

        let export_name = func.legacy_core_export_name(interface_name);

        let export_dir = self.gen.opts.gen_dir.clone();

        let mut toplevel_generator = self.gen.interface(
            self.resolve,
            export_dir.as_str(),
            self.module,
            Direction::Export,
        );

        let mut bindgen = FunctionBindgen::new(
            &mut toplevel_generator,
            &func.name,
            self.name,
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

        assert!(toplevel_generator.src.is_empty());
        assert!(toplevel_generator.ffi.is_empty());

        let result_type = match &sig.results[..] {
            [] => "Unit",
            [result] => wasm_type(*result),
            _ => unreachable!(),
        };

        let camel_name = func.name.to_upper_camel_case();

        let func_name = self.gen.export_ns.tmp(&format!("wasmExport{camel_name}"));

        let params = sig
            .params
            .iter()
            .enumerate()
            .map(|(i, param)| {
                let ty = wasm_type(*param);
                format!("p{i} : {ty}")
            })
            .collect::<Vec<_>>()
            .join(", ");

        uwrite!(
            self.ffi,
            r#"
            pub fn {func_name}({params}) -> {result_type} {{
                {src}
            }}
            "#,
        );
        self.gen.export.insert(func_name, format!("{export_name}"));

        if abi::guest_export_needs_post_return(self.resolve, func) {
            let params = sig
                .results
                .iter()
                .enumerate()
                .map(|(i, param)| {
                    let ty = wasm_type(*param);
                    format!("p{i} : {ty}")
                })
                .collect::<Vec<_>>()
                .join(", ");

            let mut bindgen = FunctionBindgen::new(
                self,
                "INVALID",
                self.name,
                (0..sig.results.len()).map(|i| format!("p{i}")).collect(),
            );

            abi::post_return(bindgen.gen.resolve, func, &mut bindgen, false);

            let src = bindgen.src;

            let func_name = self
                .gen
                .export_ns
                .tmp(&format!("wasmExport{camel_name}PostReturn"));

            uwrite!(
                self.ffi,
                r#"
                pub fn {func_name}({params}) -> Unit {{
                    {src}
                }}
                "#
            );
            self.gen
                .export
                .insert(func_name, format!("cabi_post_{export_name}"));
        }

        print_docs(&mut self.stub, &func.docs);
        uwrite!(
            self.stub,
            r#"
            {func_sig} {{
                ...
            }}
            "#
        );
    }

    fn type_name(&mut self, ty: &Type, type_variable: bool) -> String {
        match ty {
            Type::Bool => "Bool".into(),
            Type::U8 => "Byte".into(),
            Type::S32 | Type::S8 | Type::S16 => "Int".into(),
            Type::U16 | Type::U32 => "UInt".into(),
            Type::Char => "Char".into(),
            Type::U64 => "UInt64".into(),
            Type::S64 => "Int64".into(),
            Type::F32 => "Float".into(),
            Type::F64 => "Double".into(),
            Type::String => "String".into(),
            Type::Id(id) => {
                let ty = &self.resolve.types[dealias(self.resolve, *id)];
                match &ty.kind {
                    TypeDefKind::Type(ty) => self.type_name(ty, type_variable),
                    TypeDefKind::List(ty) => {
                        if type_variable {
                            match ty {
                                Type::U8
                                | Type::U32
                                | Type::U64
                                | Type::S32
                                | Type::S64
                                | Type::F32
                                | Type::F64 => {
                                    format!("FixedArray[{}]", self.type_name(ty, type_variable))
                                }
                                _ => format!("Array[{}]", self.type_name(ty, type_variable)),
                            }
                        } else {
                            "Array".into()
                        }
                    }
                    TypeDefKind::Tuple(tuple) => {
                        if type_variable {
                            format!(
                                "({})",
                                tuple
                                    .types
                                    .iter()
                                    .map(|ty| self.type_name(ty, type_variable))
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            )
                        } else {
                            unreachable!()
                        }
                    }
                    TypeDefKind::Option(ty) => {
                        if type_variable {
                            format!("{}?", self.type_name(ty, type_variable))
                        } else {
                            "Option".into()
                        }
                    }
                    TypeDefKind::Result(result) => {
                        if type_variable {
                            let mut name = |ty: &Option<Type>| {
                                ty.as_ref()
                                    .map(|ty| self.type_name(ty, true))
                                    .unwrap_or_else(|| "Unit".into())
                            };
                            let ok = name(&result.ok);
                            let err = name(&result.err);

                            format!("Result[{ok}, {err}]")
                        } else {
                            "Result".into()
                        }
                    }
                    TypeDefKind::Handle(handle) => {
                        let ty = match handle {
                            Handle::Own(ty) => ty,
                            Handle::Borrow(ty) => ty,
                        };
                        let ty = &self.resolve.types[dealias(self.resolve, *ty)];
                        if let Some(name) = &ty.name {
                            format!("{}{}", self.qualifier(ty), name.to_moonbit_type_ident())
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {
                        if let Some(name) = &ty.name {
                            format!("{}{}", self.qualifier(ty), name.to_moonbit_type_ident())
                        } else {
                            unreachable!()
                        }
                    }
                }
            }
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

    fn sig_string(&mut self, func: &Function, ignore_param: bool) -> String {
        let name = match func.kind {
            FunctionKind::Freestanding => func.name.to_moonbit_ident(),
            FunctionKind::Constructor(_) => {
                func.name.replace("[constructor]", "").to_moonbit_ident()
            }
            _ => func.name.split(".").last().unwrap().to_moonbit_ident(),
        };
        let type_name = match func.kind {
            FunctionKind::Freestanding => "".into(),
            FunctionKind::Method(ty) | FunctionKind::Constructor(ty) | FunctionKind::Static(ty) => {
                format!("{}::", self.type_name(&Type::Id(ty), true))
            }
        };

        let result_type = match func.results.len() {
            0 => "Unit".into(),
            1 => self.type_name(func.results.iter_types().next().unwrap(), true),
            _ => {
                format!(
                    "({})",
                    func.results
                        .iter_types()
                        .map(|ty| self.type_name(ty, true))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        };

        let params = func
            .params
            .iter()
            .map(|(name, ty)| {
                let ty = self.type_name(ty, true);
                let name = if ignore_param {
                    format!("_{}", name.to_moonbit_ident())
                } else {
                    name.to_moonbit_ident()
                };
                format!("{name} : {ty}")
            })
            .collect::<Vec<_>>()
            .join(", ");

        format!("pub fn {type_name}{name}({params}) -> {result_type}")
    }
}

impl<'a> wit_bindgen_core::InterfaceGenerator<'a> for InterfaceGenerator<'a> {
    fn resolve(&self) -> &'a Resolve {
        self.resolve
    }

    fn type_record(&mut self, _id: TypeId, name: &str, record: &Record, docs: &Docs) {
        print_docs(&mut self.src, docs);

        let name = name.to_moonbit_type_ident();

        let parameters = record
            .fields
            .iter()
            .map(|field| {
                format!(
                    "{} : {}",
                    field.name.to_moonbit_ident(),
                    self.type_name(&field.ty, true),
                )
            })
            .collect::<Vec<_>>()
            .join("; ");

        let mut deriviation: Vec<_> = Vec::new();
        if self.gen.opts.derive_show {
            deriviation.push("Show")
        }
        if self.gen.opts.derive_eq {
            deriviation.push("Eq")
        }

        uwrite!(
            self.src,
            "
            pub(all) struct {name} {{
                {parameters}
            }} derive({})
            ",
            deriviation.join(", ")
        );
    }

    fn type_resource(&mut self, _id: TypeId, name: &str, docs: &Docs) {
        print_docs(&mut self.src, docs);
        let type_name = name;
        let name = name.to_moonbit_type_ident();

        let mut deriviation: Vec<_> = Vec::new();
        if self.gen.opts.derive_show {
            deriviation.push("Show")
        }
        if self.gen.opts.derive_eq {
            deriviation.push("Eq")
        }
        let declaration = if self.gen.opts.derive_error && name.contains("Error") {
            "type!"
        } else {
            "type"
        };

        uwrite!(
            self.src,
            r#"
            pub(all) {declaration} {name} Int derive({})
            "#,
            deriviation.join(", "),
        );

        let module = self.module;

        if self.direction == Direction::Import {
            uwrite!(
                &mut self.src,
                r#"
                /// Drops a resource handle.
                pub fn {name}::drop(self : {name}) -> Unit {{
                    let {name}(resource) = self
                    wasmImportResourceDrop{name}(resource)
                }}
                "#,
            );

            uwrite!(
                &mut self.ffi,
                r#"
                fn wasmImportResourceDrop{name}(resource : Int) = "{module}" "[resource-drop]{type_name}"
                "#,
            )
        } else {
            uwrite!(
                &mut self.src,
                r#"
                /// Creates a new resource with the given `rep` as its representation and returning the handle to this resource.
                pub fn {name}::new(rep : Int) -> {name} {{
                    {name}::{name}(wasmExportResourceNew{name}(rep))
                }}
                fn wasmExportResourceNew{name}(rep : Int) -> Int = "[export]{module}" "[resource-new]{type_name}"

                /// Drops a resource handle.
                pub fn {name}::drop(self : {name}) -> Unit {{
                    let {name}(resource) = self
                    wasmExportResourceDrop{name}(resource)
                }}
                fn wasmExportResourceDrop{name}(resource : Int) = "[export]{module}" "[resource-drop]{type_name}"

                /// Gets the `Int` representation of the resource pointed to the given handle.
                pub fn {name}::rep(self : {name}) -> Int {{
                    let {name}(resource) = self
                    wasmExportResourceRep{name}(resource)
                }}
                fn wasmExportResourceRep{name}(resource : Int) -> Int = "[export]{module}" "[resource-rep]{type_name}"
                "#,
            );

            uwrite!(
                &mut self.stub,
                r#"
                /// Destructor of the resource.
                pub fn {name}::dtor(_self : {name}) -> Unit {{
                  ...
                }}
                "#
            );

            let func_name = self.gen.export_ns.tmp(&format!("wasmExport{name}Dtor"));

            let export_dir = self.gen.opts.gen_dir.clone();

            let mut gen =
                self.gen
                    .interface(self.resolve, export_dir.as_str(), "", Direction::Export);

            uwrite!(
                self.ffi,
                r#"
                pub fn {func_name}(handle : Int) -> Unit {{
                    {}{name}::dtor(handle)
                }}
                "#,
                gen.qualify_package(&self.name.to_string())
            );

            self.gen
                .export
                .insert(func_name, format!("{module}#[dtor]{type_name}"));
        }
    }

    fn type_flags(&mut self, _id: TypeId, name: &str, flags: &Flags, docs: &Docs) {
        print_docs(&mut self.src, docs);

        let name = name.to_moonbit_type_ident();

        let ty = match flags.repr() {
            FlagsRepr::U8 => "Byte",
            FlagsRepr::U16 | FlagsRepr::U32(1) => "UInt",
            FlagsRepr::U32(2) => "UInt64",
            _ => unreachable!(), // https://github.com/WebAssembly/component-model/issues/370
        };

        let cases = flags
            .flags
            .iter()
            .map(|flag| flag.name.to_shouty_snake_case())
            .collect::<Vec<_>>()
            .join("; ");

        let map_to_int = flags
            .flags
            .iter()
            .enumerate()
            .map(|(i, flag)| {
                let flag_name = flag.name.to_shouty_snake_case();
                let suffix = if matches!(flags.repr(), FlagsRepr::U32(2)) {
                    "UL"
                } else {
                    "U"
                };
                let cast = if matches!(flags.repr(), FlagsRepr::U8) {
                    ".to_byte()"
                } else {
                    ""
                };
                format!("{flag_name} => ((1{suffix} << {i}){cast})")
            })
            .collect::<Vec<_>>()
            .join("\n    ");

        let mut deriviation: Vec<_> = Vec::new();
        if self.gen.opts.derive_show {
            deriviation.push("Show")
        }
        if self.gen.opts.derive_eq {
            deriviation.push("Eq")
        }
        let declaration = if self.gen.opts.derive_error && name.contains("Error") {
            "type!"
        } else {
            "type"
        };

        uwrite!(
            self.src,
            "
            pub(all) {declaration} {name} {ty} derive({})
            pub fn {name}::default() -> {name} {{
                {}
            }}
            pub(all) enum {name}Flag {{
                {cases}
            }}
            fn {name}Flag::value(self : {name}Flag) -> {ty} {{
              match self {{
                {map_to_int}
              }}
            }}
            pub fn {name}::set(self : {name}, other: {name}Flag) -> {name} {{
              let {name}(flag) = self
              flag.lor(other.value())
            }}
            pub fn {name}::unset(self : {name}, other: {name}Flag) -> {name} {{
              let {name}(flag) = self
              flag.land(other.value().lnot())
            }}
            pub fn {name}::is_set(self : {name}, other: {name}Flag) -> Bool {{
              let {name}(flag) = self
              (flag.land(other.value()) == other.value())
            }}
            ",
            deriviation.join(", "),
            match ty {
                "Byte" => "b'\\x00'",
                "UInt" => "0U",
                "UInt64" => "0UL",
                _ => unreachable!(),
            }
        );
    }

    fn type_tuple(&mut self, _id: TypeId, _name: &str, _tuple: &Tuple, _docs: &Docs) {
        // Not needed
    }

    fn type_variant(&mut self, _id: TypeId, name: &str, variant: &Variant, docs: &Docs) {
        print_docs(&mut self.src, docs);

        let name = name.to_moonbit_type_ident();

        let cases = variant
            .cases
            .iter()
            .map(|case| {
                let name = case.name.to_upper_camel_case();
                if let Some(ty) = case.ty {
                    let ty = self.type_name(&ty, true);
                    format!("{name}({ty})")
                } else {
                    format!("{name}")
                }
            })
            .collect::<Vec<_>>()
            .join("\n  ");

        let mut deriviation: Vec<_> = Vec::new();
        if self.gen.opts.derive_show {
            deriviation.push("Show")
        }
        if self.gen.opts.derive_eq {
            deriviation.push("Eq")
        }
        let declaration = if self.gen.opts.derive_error && name.contains("Error") {
            "type!"
        } else {
            "enum"
        };

        uwrite!(
            self.src,
            "
            pub(all) {declaration} {name} {{
              {cases}
            }} derive({})
            ",
            deriviation.join(", ")
        );
    }

    fn type_option(&mut self, _id: TypeId, _name: &str, _payload: &Type, _docs: &Docs) {
        // Not needed
    }

    fn type_result(&mut self, _id: TypeId, _name: &str, _result: &Result_, _docs: &Docs) {
        // Not needed
    }

    fn type_enum(&mut self, _id: TypeId, name: &str, enum_: &Enum, docs: &Docs) {
        print_docs(&mut self.src, docs);

        let name = name.to_moonbit_type_ident();

        // Type definition
        let cases = enum_
            .cases
            .iter()
            .map(|case| case.name.to_shouty_snake_case())
            .collect::<Vec<_>>()
            .join("; ");

        let mut deriviation: Vec<_> = Vec::new();
        if self.gen.opts.derive_show {
            deriviation.push("Show")
        }
        if self.gen.opts.derive_eq {
            deriviation.push("Eq")
        }
        let declaration = if self.gen.opts.derive_error && name.contains("Error") {
            "type!"
        } else {
            "enum"
        };

        uwrite!(
            self.src,
            "
            pub(all) {declaration} {name} {{
                {cases}
            }} derive({})
            ",
            deriviation.join(", ")
        );

        // Case to integer
        let cases = enum_
            .cases
            .iter()
            .enumerate()
            .map(|(i, case)| format!("{} => {i}", case.name.to_shouty_snake_case()))
            .collect::<Vec<_>>()
            .join("\n  ");

        uwrite!(
            self.src,
            "
            pub fn {name}::ordinal(self : {name}) -> Int {{
              match self {{
                {cases}
              }}
            }}
            "
        );

        // Integer to case
        let cases = enum_
            .cases
            .iter()
            .enumerate()
            .map(|(i, case)| format!("{i} => {}", case.name.to_shouty_snake_case()))
            .collect::<Vec<_>>()
            .join("\n  ");

        uwrite!(
            self.src,
            "
            pub fn {name}::from(self : Int) -> {name} {{
              match self {{
                {cases}
                _ => panic()
              }}
            }}
            "
        );
    }

    fn type_alias(&mut self, _id: TypeId, _name: &str, _ty: &Type, _docs: &Docs) {
        // TODO: Implement correct type aliasing
        // self.type_name(&Type::Id(id));
    }

    fn type_list(&mut self, _id: TypeId, _name: &str, _ty: &Type, _docs: &Docs) {
        // Not needed
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
enum Cleanup {
    Memory {
        address: String,
        size: String,
        align: usize,
    },
    Object(String),
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
    func_interface: &'b str,
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
        func_interface: &'b str,
        params: Box<[String]>,
    ) -> FunctionBindgen<'a, 'b> {
        let mut locals = Ns::default();
        params.iter().for_each(|str| {
            locals.tmp(str);
        });
        Self {
            gen,
            func_name,
            func_interface,
            params,
            src: String::new(),
            locals,
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
        is_result: bool,
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

        let declarations = lowered.join(",");

        let cases = cases
            .iter()
            .zip(blocks)
            .zip(payloads)
            .map(|(((name, ty), Block { body, results, .. }), payload)| {
                let name = name.to_upper_camel_case();
                let assignments = results
                    .iter()
                    .map(|result| format!("{result}"))
                    .collect::<Vec<_>>()
                    .join(", ");

                let payload = if self.gen.non_empty_type(ty.as_ref()).is_some() {
                    payload
                } else if is_result {
                    format!("_{payload}")
                } else {
                    String::new()
                };

                if payload.is_empty() {
                    format!(
                        "{name} => {{
                          {body}
                          ({assignments})
                        }}"
                    )
                } else {
                    format!(
                        "{name}({payload}) => {{
                          {body}
                          ({assignments})
                        }}",
                    )
                }
            })
            .collect::<Vec<_>>()
            .join("\n");

        if declarations.is_empty() {
            uwrite!(
                self.src,
                r#"
                match {op} {{
                    {cases}
                }}
                "#
            );
        } else {
            uwrite!(
                self.src,
                r#"
                let ({declarations}) = match {op} {{
                    {cases}
                }}
                "#
            );
        }
    }

    fn lift_variant(
        &mut self,
        ty: &Type,
        cases: &[(&str, Option<Type>)],
        op: &str,
        results: &mut Vec<String>,
        is_result: bool,
    ) {
        let blocks = self
            .blocks
            .drain(self.blocks.len() - cases.len()..)
            .collect::<Vec<_>>();

        // Hacky way to get the type name without type parameter
        let ty = self.gen.type_name(ty, false);
        let lifted = self.locals.tmp("lifted");

        let cases = cases
            .iter()
            .zip(blocks)
            .enumerate()
            .map(|(i, ((case_name, case_ty), Block { body, results, .. }))| {
                let payload = if self.gen.non_empty_type(case_ty.as_ref()).is_some() {
                    results.into_iter().next().unwrap()
                } else {
                    String::new()
                };

                let constructor = format!("{ty}::{}", case_name.to_upper_camel_case());

                if payload.is_empty() && !is_result {
                    format!(
                        "{i} => {{
                             {body}
                             {constructor}
                         }}"
                    )
                } else {
                    format!(
                        "{i} => {{
                             {body}
                             {constructor}({})
                         }}",
                        if payload.is_empty() {
                            "()".into()
                        } else {
                            payload
                        }
                    )
                }
            })
            .collect::<Vec<_>>()
            .join("\n");

        uwrite!(
            self.src,
            r#"
            let {lifted} = match ({op}) {{
                {cases}
                _ => panic()
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
            Instruction::I32Const { val } => results.push(format!("({})", val.to_string())),
            Instruction::ConstZero { tys } => results.extend(tys.iter().map(|ty| {
                match ty {
                    WasmType::I32 => "0",
                    WasmType::I64 => "0L",
                    WasmType::F32 => "(0.0 : Float)",
                    WasmType::F64 => "0.0",
                    WasmType::Pointer => "0",
                    WasmType::PointerOrI64 => "0L",
                    WasmType::Length => "0",
                }
                .to_owned()
            })),

            Instruction::Bitcasts { casts } => results.extend(
                casts
                    .iter()
                    .zip(operands)
                    .map(|(cast, op)| perform_cast(op, cast)),
            ),

            Instruction::I32FromS32
            | Instruction::I64FromS64
            | Instruction::S32FromI32
            | Instruction::S64FromI64
            | Instruction::CoreF64FromF64
            | Instruction::F64FromCoreF64 => results.push(operands[0].clone()),

            Instruction::F32FromCoreF32 => results.push(operands[0].clone()),
            Instruction::CoreF32FromF32 => results.push(operands[0].clone()),

            Instruction::CharFromI32 => results.push(format!("Char::from_int({})", operands[0])),
            Instruction::I32FromChar => results.push(format!("({}).to_int()", operands[0])),

            Instruction::I32FromU8 => results.push(format!("({}).to_int()", operands[0])),
            Instruction::I32FromU16 => {
                results.push(format!("({}).reinterpret_as_int()", operands[0]))
            }
            Instruction::U8FromI32 => results.push(format!("({}).to_byte()", operands[0])),

            Instruction::I32FromS8 => results.push(format!(
                "{}extend8({})",
                self.gen.qualify_package(FFI_DIR),
                operands[0]
            )),
            Instruction::S8FromI32 => results.push(format!("({} - 0x100)", operands[0])),
            Instruction::S16FromI32 => results.push(format!("({} - 0x10000)", operands[0])),
            Instruction::I32FromS16 => results.push(format!(
                "{}extend16({})",
                self.gen.qualify_package(FFI_DIR),
                operands[0]
            )),
            Instruction::U16FromI32 => results.push(format!(
                "({}.land(0xFFFF).reinterpret_as_uint())",
                operands[0]
            )),
            Instruction::U32FromI32 => {
                results.push(format!("({}).reinterpret_as_uint()", operands[0]))
            }
            Instruction::I32FromU32 => {
                results.push(format!("({}).reinterpret_as_int()", operands[0]))
            }

            Instruction::U64FromI64 => {
                results.push(format!("({}).reinterpret_as_uint64()", operands[0]))
            }
            Instruction::I64FromU64 => {
                results.push(format!("({}).reinterpret_as_int64()", operands[0]))
            }

            Instruction::I32FromBool => {
                results.push(format!("(if {} {{ 1 }} else {{ 0 }})", operands[0]));
            }
            Instruction::BoolFromI32 => results.push(format!("({} != 0)", operands[0])),

            Instruction::FlagsLower { flags, ty, .. } => match flags_repr(flags) {
                Int::U8 => {
                    let op = &operands[0];
                    let flag = self.locals.tmp("flag");
                    let ty = self.gen.type_name(&Type::Id(*ty), false);
                    uwriteln!(
                        self.src,
                        r#"
                        let {ty}({flag}) = {op}
                        "#
                    );
                    results.push(format!("{flag}.to_int()"));
                }
                Int::U16 | Int::U32 => {
                    let op = &operands[0];
                    let flag = self.locals.tmp("flag");
                    let ty = self.gen.type_name(&Type::Id(*ty), false);
                    uwriteln!(
                        self.src,
                        r#"
                        let {ty}({flag}) = {op}
                        "#
                    );
                    results.push(format!("{flag}.reinterpret_as_int()"));
                }
                Int::U64 => {
                    let op = &operands[0];
                    let flag = self.locals.tmp("flag");
                    let ty = self.gen.type_name(&Type::Id(*ty), false);
                    uwriteln!(
                        self.src,
                        r#"
                        let {ty}({flag}) = {op}
                        "#
                    );
                    results.push(format!("({flag}.to_int())"));
                    results.push(format!("({flag}.lsr(32)).to_int())"));
                }
            },

            Instruction::FlagsLift { flags, ty, .. } => match flags_repr(flags) {
                Int::U8 => {
                    results.push(format!(
                        "{}({}.to_byte())",
                        self.gen.type_name(&Type::Id(*ty), true),
                        operands[0]
                    ));
                }
                Int::U16 | Int::U32 => {
                    results.push(format!(
                        "{}({}.reinterpret_as_uint())",
                        self.gen.type_name(&Type::Id(*ty), true),
                        operands[0]
                    ));
                }
                Int::U64 => {
                    results.push(format!(
                        "{}(({}).reinterpret_as_uint().to_uint64() | (({}).reinterpret_as_uint().to_uint64() << 32))",
                        self.gen.type_name(&Type::Id(*ty), true),
                        operands[0],
                        operands[1]
                    ));
                }
            },

            Instruction::HandleLower { ty, .. } => {
                let op = &operands[0];
                let handle = self.locals.tmp("handle");
                let ty = self.gen.type_name(&Type::Id(*ty), false);
                uwrite!(
                    self.src,
                    r#"
                    let {ty}({handle}) = {op}
                    "#
                );
                results.push(handle);
            }
            Instruction::HandleLift { ty, .. } => {
                let op = &operands[0];
                let ty = self.gen.type_name(&Type::Id(*ty), false);

                results.push(format!(
                    "{}::{}({})",
                    ty,
                    if ty.starts_with("@") {
                        ty.split('.').last().unwrap()
                    } else {
                        &ty
                    },
                    op
                ));
            }

            Instruction::RecordLower { record, .. } => {
                let op = &operands[0];
                for field in record.fields.iter() {
                    results.push(format!("({op}).{}", field.name.to_moonbit_ident()));
                }
            }
            Instruction::RecordLift { ty, record, .. } => {
                let ops = operands
                    .iter()
                    .enumerate()
                    .map(|(i, op)| {
                        format!(
                            "{} : {}",
                            record.fields[i].name.to_moonbit_ident(),
                            op.to_string()
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(", ");

                results.push(format!(
                    "{}::{{{ops}}}",
                    self.gen.type_name(&Type::Id(*ty), true)
                ));
            }

            Instruction::TupleLower { tuple, .. } => {
                let op = &operands[0];
                // Empty tuple is Unit
                // (T) is T
                if tuple.types.len() == 0 {
                    results.push("()".into());
                } else if tuple.types.len() == 1 {
                    results.push(format!("{}", operands[0]));
                } else {
                    for i in 0..tuple.types.len() {
                        results.push(format!("({op}).{i}"));
                    }
                }
            }
            Instruction::TupleLift { .. } => {
                let ops = operands
                    .iter()
                    .map(|op| op.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                results.push(format!("({ops})"));
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
                false,
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
                false,
            ),

            Instruction::OptionLower {
                results: lowered_types,
                ..
            } => {
                let some = self.blocks.pop().unwrap();
                let none = self.blocks.pop().unwrap();
                let some_payload = self.payloads.pop().unwrap();
                let _none_payload = self.payloads.pop().unwrap();

                let lowered = lowered_types
                    .iter()
                    .map(|_| self.locals.tmp("lowered"))
                    .collect::<Vec<_>>();

                results.extend(lowered.iter().cloned());

                let declarations = lowered
                    .iter()
                    .map(|lowered| format!("{lowered}"))
                    .collect::<Vec<_>>()
                    .join(", ");

                let op = &operands[0];

                let block = |Block { body, results, .. }| {
                    let assignments = results
                        .iter()
                        .map(|result| format!("{result}"))
                        .collect::<Vec<_>>()
                        .join(", ");

                    format!(
                        "{body}
                         ({assignments})"
                    )
                };

                let none = block(none);
                let some = block(some);

                if declarations.is_empty() {
                    uwrite!(
                        self.src,
                        r#"
                        match (({op})) {{
                            None => {{
                                {none}
                            }}
                            Some({some_payload}) => {{
                                {some}
                            }}
                        }}
                        "#
                    );
                } else {
                    uwrite!(
                        self.src,
                        r#"
                        let ({declarations}) = match (({op})) {{
                            None => {{
                                {none}
                            }}
                            Some({some_payload}) => {{
                                {some}
                            }}
                        }}
                        "#
                    );
                }
            }

            Instruction::OptionLift { payload, ty } => {
                let some = self.blocks.pop().unwrap();
                let _none = self.blocks.pop().unwrap();

                let ty = self.gen.type_name(&Type::Id(*ty), true);
                let lifted = self.locals.tmp("lifted");
                let op = &operands[0];

                let payload = if self.gen.non_empty_type(Some(*payload)).is_some() {
                    some.results.into_iter().next().unwrap()
                } else {
                    "None".into()
                };

                let some = some.body;

                uwrite!(
                    self.src,
                    r#"
                    let {lifted} : {ty} = match {op} {{
                        0 => Option::None
                        1 => {{
                            {some}
                            Option::Some({payload})
                        }}
                        _ => panic()
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
                &[("Ok", result.ok), ("Err", result.err)],
                lowered_types,
                &operands[0],
                results,
                true,
            ),

            Instruction::ResultLift { result, ty } => self.lift_variant(
                &Type::Id(*ty),
                &[("Ok", result.ok), ("Err", result.err)],
                &operands[0],
                results,
                true,
            ),

            Instruction::EnumLower { .. } => results.push(format!("{}.ordinal()", operands[0])),

            Instruction::EnumLift { ty, .. } => results.push(format!(
                "{}::from({})",
                self.gen.type_name(&Type::Id(*ty), true),
                operands[0]
            )),

            Instruction::ListCanonLower { element, realloc } => match element {
                Type::U8 => {
                    let op = &operands[0];

                    results.push(format!(
                        "{}bytes2ptr({op})",
                        self.gen.qualify_package(FFI_DIR)
                    ));
                    results.push(format!("{op}.length()"));
                    if realloc.is_none() {
                        self.cleanup.push(Cleanup::Object(op.clone()));
                    }
                }
                Type::U32 | Type::U64 | Type::S32 | Type::S64 | Type::F32 | Type::F64 => {
                    let op = &operands[0];

                    let ty = match element {
                        Type::U32 => "uint",
                        Type::U64 => "uint64",
                        Type::S32 => "int",
                        Type::S64 => "int64",
                        Type::F32 => "float",
                        Type::F64 => "double",
                        _ => unreachable!(),
                    };

                    results.push(format!(
                        "{}{ty}_array2ptr({op})",
                        self.gen.qualify_package(FFI_DIR)
                    ));
                    results.push(format!("{op}.length()"));
                    if realloc.is_none() {
                        self.cleanup.push(Cleanup::Object(op.clone()));
                    }
                }
                _ => unreachable!("unsupported list element type"),
            },

            Instruction::ListCanonLift { element, .. } => match element {
                Type::U8 => {
                    let result = self.locals.tmp("result");
                    let address = &operands[0];
                    let length = &operands[1];

                    uwrite!(
                        self.src,
                        "
                        let {result} = {}ptr2bytes({address}, {length})
                        ",
                        self.gen.qualify_package(FFI_DIR)
                    );

                    results.push(result);
                }
                Type::U32 | Type::U64 | Type::S32 | Type::S64 | Type::F32 | Type::F64 => {
                    let ty = match element {
                        Type::U32 => "uint",
                        Type::U64 => "uint64",
                        Type::S32 => "int",
                        Type::S64 => "int64",
                        Type::F32 => "float",
                        Type::F64 => "double",
                        _ => unreachable!(),
                    };

                    let result = self.locals.tmp("result");
                    let address = &operands[0];
                    let length = &operands[1];

                    uwrite!(
                        self.src,
                        "
                        let {result} = {}ptr2{ty}_array({address}, {length})
                        ",
                        self.gen.qualify_package(FFI_DIR)
                    );

                    results.push(result);
                }
                _ => unreachable!("unsupported list element type"),
            },

            Instruction::StringLower { realloc } => {
                let op = &operands[0];

                results.push(format!(
                    "{}str2ptr({op})",
                    self.gen.qualify_package(FFI_DIR)
                ));
                results.push(format!("{op}.iter().count()"));
                if realloc.is_none() {
                    self.cleanup.push(Cleanup::Object(op.clone()));
                }
            }

            Instruction::StringLift { .. } => {
                let result = self.locals.tmp("result");
                let address = &operands[0];
                let length = &operands[1];

                uwrite!(
                    self.src,
                    "
                    ignore({length})
                    let {result} = {}ptr2str({address})
                    ",
                    self.gen.qualify_package(FFI_DIR)
                );

                results.push(result);
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
                let size = self.gen.gen.sizes.size(element).size_wasm32();
                let align = self.gen.gen.sizes.align(element).align_wasm32();
                let address = self.locals.tmp("address");
                let ty = self.gen.type_name(element, true);
                let index = self.locals.tmp("index");

                uwrite!(
                    self.src,
                    "
                    let {address} = {}malloc(({op}).length() * {size});
                    for {index} = 0; {index} < ({op}).length(); {index} = {index} + 1 {{
                        let {block_element} : {ty} = ({op})[({index})]
                        let {base} = {address} + ({index} * {size});
                        {body}
                    }}
                    ",
                    self.gen.qualify_package(FFI_DIR)
                );

                if realloc.is_none() {
                    self.cleanup.push(Cleanup::Memory {
                        address: address.clone(),
                        size: format!("({op}).length() * {size}"),
                        align,
                    });
                }

                results.push(address);
                results.push(format!("({op}).length()"));
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
                let ty = self.gen.type_name(element, true);
                let size = self.gen.gen.sizes.size(element).size_wasm32();
                // let align = self.gen.gen.sizes.align(element);
                let index = self.locals.tmp("index");

                let result = match &block_results[..] {
                    [result] => result,
                    _ => todo!("result count == {}", results.len()),
                };

                uwrite!(
                    self.src,
                    "
                    let {array} : Array[{ty}] = [];
                    for {index} = 0; {index} < ({length}); {index} = {index} + 1 {{
                        let {base} = ({address}) + ({index} * {size})
                        {body}
                        {array}.push({result})
                    }}
                    {}free({address})
                    ",
                    self.gen.qualify_package(FFI_DIR)
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
                        let assignment = format!("let {result} : {ty} = ");
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
                let assignment = match func.results.len() {
                    0 => "let _ = ".into(),
                    _ => {
                        let ty = format!(
                            "({})",
                            func.results
                                .iter_types()
                                .map(|ty| self.gen.type_name(ty, true))
                                .collect::<Vec<_>>()
                                .join(", ")
                        );

                        let result = func
                            .results
                            .iter_types()
                            .map(|_ty| {
                                let result = self.locals.tmp("result");
                                results.push(result.clone());
                                result
                            })
                            .collect::<Vec<_>>()
                            .join(", ");

                        let assignment = format!("let ({result}) : {ty} = ");

                        assignment
                    }
                };

                let name = match func.kind {
                    FunctionKind::Freestanding => {
                        format!(
                            "{}{}",
                            self.r#gen.qualify_package(&self.func_interface.to_string()),
                            func.name.to_moonbit_ident()
                        )
                    }
                    FunctionKind::Constructor(ty) => {
                        let name = self.gen.type_name(&Type::Id(ty), false);
                        format!(
                            "{}::{}",
                            name,
                            func.name.replace("[constructor]", "").to_moonbit_ident()
                        )
                    }
                    FunctionKind::Method(ty) | FunctionKind::Static(ty) => {
                        let name = self.gen.type_name(&Type::Id(ty), false);
                        format!(
                            "{}::{}",
                            name,
                            func.name.split(".").last().unwrap().to_moonbit_ident()
                        )
                    }
                };

                let args = operands.join(", ");

                uwrite!(
                    self.src,
                    "
                    {assignment}{name}({args});
                    ",
                );
            }

            Instruction::Return { amt, .. } => {
                for clean in &self.cleanup {
                    match clean {
                        Cleanup::Memory {
                            address,
                            size: _,
                            align: _,
                        } => uwriteln!(
                            self.src,
                            "{}free({address})",
                            self.gen.qualify_package(FFI_DIR)
                        ),
                        Cleanup::Object(obj) => uwriteln!(self.src, "ignore({obj})"),
                    }
                }

                if self.needs_cleanup_list {
                    uwrite!(
                        self.src,
                        "
                        cleanupList.each(fn(cleanup) {{
                            {}free(cleanup.address);
                        }})
                        ignore(ignoreList)
                        ",
                        self.gen.qualify_package(FFI_DIR)
                    );
                }

                match *amt {
                    0 => (),
                    1 => uwriteln!(self.src, "return {}", operands[0]),
                    _ => {
                        let results = operands.join(", ");
                        uwriteln!(self.src, "return ({results})");
                    }
                }
            }

            Instruction::I32Load { offset }
            | Instruction::PointerLoad { offset }
            | Instruction::LengthLoad { offset } => results.push(format!(
                "{}load32(({}) + {offset})",
                self.gen.qualify_package(FFI_DIR),
                operands[0],
                offset = offset.size_wasm32()
            )),

            Instruction::I32Load8U { offset } => results.push(format!(
                "{}load8_u(({}) + {offset})",
                self.gen.qualify_package(FFI_DIR),
                operands[0],
                offset = offset.size_wasm32()
            )),

            Instruction::I32Load8S { offset } => results.push(format!(
                "{}load8(({}) + {offset})",
                self.gen.qualify_package(FFI_DIR),
                operands[0],
                offset = offset.size_wasm32()
            )),

            Instruction::I32Load16U { offset } => results.push(format!(
                "{}load16_u(({}) + {offset})",
                self.gen.qualify_package(FFI_DIR),
                operands[0],
                offset = offset.size_wasm32()
            )),

            Instruction::I32Load16S { offset } => results.push(format!(
                "{}load16(({}) + {offset})",
                self.gen.qualify_package(FFI_DIR),
                operands[0],
                offset = offset.size_wasm32()
            )),

            Instruction::I64Load { offset } => results.push(format!(
                "{}load64(({}) + {offset})",
                self.gen.qualify_package(FFI_DIR),
                operands[0],
                offset = offset.size_wasm32()
            )),

            Instruction::F32Load { offset } => results.push(format!(
                "{}loadf32(({}) + {offset})",
                self.gen.qualify_package(FFI_DIR),
                operands[0],
                offset = offset.size_wasm32()
            )),

            Instruction::F64Load { offset } => results.push(format!(
                "{}loadf64(({}) + {offset})",
                self.gen.qualify_package(FFI_DIR),
                operands[0],
                offset = offset.size_wasm32()
            )),

            Instruction::I32Store { offset }
            | Instruction::PointerStore { offset }
            | Instruction::LengthStore { offset } => uwriteln!(
                self.src,
                "{}store32(({}) + {offset}, {})",
                self.gen.qualify_package(FFI_DIR),
                operands[1],
                operands[0],
                offset = offset.size_wasm32()
            ),

            Instruction::I32Store8 { offset } => uwriteln!(
                self.src,
                "{}store8(({}) + {offset}, {})",
                self.gen.qualify_package(FFI_DIR),
                operands[1],
                operands[0],
                offset = offset.size_wasm32()
            ),

            Instruction::I32Store16 { offset } => uwriteln!(
                self.src,
                "{}store16(({}) + {offset}, {})",
                self.gen.qualify_package(FFI_DIR),
                operands[1],
                operands[0],
                offset = offset.size_wasm32()
            ),

            Instruction::I64Store { offset } => uwriteln!(
                self.src,
                "{}store64(({}) + {offset}, {})",
                self.gen.qualify_package(FFI_DIR),
                operands[1],
                operands[0],
                offset = offset.size_wasm32()
            ),

            Instruction::F32Store { offset } => uwriteln!(
                self.src,
                "{}storef32(({}) + {offset}, {})",
                self.gen.qualify_package(FFI_DIR),
                operands[1],
                operands[0],
                offset = offset.size_wasm32()
            ),

            Instruction::F64Store { offset } => uwriteln!(
                self.src,
                "{}storef64(({}) + {offset}, {})",
                self.gen.qualify_package(FFI_DIR),
                operands[1],
                operands[0],
                offset = offset.size_wasm32()
            ),
            // TODO: see what we can do with align
            Instruction::Malloc { size, .. } => {
                uwriteln!(
                    self.src,
                    "{}malloc({})",
                    self.gen.qualify_package(FFI_DIR),
                    size.size_wasm32()
                )
            }

            Instruction::GuestDeallocate { .. } => {
                uwriteln!(
                    self.src,
                    "{}free({})",
                    self.gen.qualify_package(FFI_DIR),
                    operands[0]
                )
            }

            Instruction::GuestDeallocateString => {
                uwriteln!(
                    self.src,
                    "{}free({})",
                    self.gen.qualify_package(FFI_DIR),
                    operands[0]
                )
            }

            Instruction::GuestDeallocateVariant { blocks } => {
                let cases = self
                    .blocks
                    .drain(self.blocks.len() - blocks..)
                    .enumerate()
                    .map(|(i, Block { body, results, .. })| {
                        assert!(results.is_empty());
                        if body.is_empty() {
                            format!("{i} => ()")
                        } else {
                            format!(
                                "{i} => {{
                                   {body}
                                 }}"
                            )
                        }
                    })
                    .collect::<Vec<_>>()
                    .join("\n");

                let op = &operands[0];

                uwrite!(
                    self.src,
                    "
                    match ({op}) {{
                        {cases}
                        _ => panic()
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
                // let align = self.gen.gen.sizes.align(element);

                if !body.trim().is_empty() {
                    let index = self.locals.tmp("index");

                    uwrite!(
                        self.src,
                        "
                        for {index} = 0; {index} < ({length}); {index} = {index} + 1 {{
                            let {base} = ({address}) + ({index} * {size})
                            {body}
                        }}
                        "
                    );
                }

                uwriteln!(
                    self.src,
                    "{}free({address})",
                    self.gen.qualify_package(FFI_DIR)
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
        if self.gen.direction == Direction::Import {
            let ffi_qualifier = self.gen.qualify_package(FFI_DIR);
            let address = self.locals.tmp("return_area");
            uwriteln!(
                self.src,
                "let {address} = {ffi_qualifier}malloc({})",
                size.size_wasm32(),
            );
            self.cleanup.push(Cleanup::Memory {
                address: address.clone(),
                size: size.size_wasm32().to_string(),
                align: align.align_wasm32(),
            });
            address
        } else {
            self.gen.gen.return_area_size = self.gen.gen.return_area_size.max(size);
            self.gen.gen.return_area_align = self.gen.gen.return_area_align.max(align);
            "return_area".into()
        }
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

            for cleanup in &self.cleanup {
                match cleanup {
                    Cleanup::Memory {
                        address,
                        size,
                        align,
                    } => uwriteln!(
                        self.src,
                        "cleanupList.push({{address: {address}, size: {size}, align: {align}}})",
                    ),
                    Cleanup::Object(obj) => uwriteln!(self.src, "ignoreList.push({obj})",),
                }
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
        matches!(
            element,
            Type::U8 | Type::U32 | Type::U64 | Type::S32 | Type::S64 | Type::F32 | Type::F64
        )
    }
}

fn perform_cast(op: &str, cast: &Bitcast) -> String {
    match cast {
        Bitcast::I32ToF32 => {
            format!("({op}).to_float()")
        }
        Bitcast::I64ToF32 => format!("Int64::to_int({op}).to_float()"),
        Bitcast::F32ToI32 => {
            format!("@ffi.f32_to_i32({op})")
        }
        Bitcast::F32ToI64 => format!("@ffi.f32_to_i64({op})"),
        Bitcast::I64ToF64 => {
            format!("Int64::to_double({op})")
        }
        Bitcast::F64ToI64 => {
            format!("Double::to_int64({op})")
        }
        Bitcast::LToI64 | Bitcast::PToP64 | Bitcast::I32ToI64 => format!("Int::to_int64({op})"),
        Bitcast::I64ToL | Bitcast::P64ToP | Bitcast::I64ToI32 => format!("Int64::to_int({op})"),
        Bitcast::I64ToP64
        | Bitcast::P64ToI64
        | Bitcast::I32ToP
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

fn wasm_type(ty: WasmType) -> &'static str {
    match ty {
        WasmType::I32 => "Int",
        WasmType::I64 => "Int64",
        WasmType::F32 => "Float",
        WasmType::F64 => "Double",
        WasmType::Pointer => "Int",
        WasmType::PointerOrI64 => "Int64",
        WasmType::Length => "Int",
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

fn indent(code: &str) -> Source {
    let mut indented = Source::default();
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
            indented.deindent(2)
        }
        indented.push_str(trimmed);
        if trimmed.ends_with('{') && !trimmed.starts_with("///") {
            indented.indent(2)
        }
        indented.push_str("\n");
    }
    indented
}

fn world_name(resolve: &Resolve, world: WorldId) -> String {
    format!("world.{}", resolve.worlds[world].name.to_lower_camel_case())
}

fn interface_name(resolve: &Resolve, name: &WorldKey) -> String {
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
    .to_lower_camel_case();

    format!(
        "interface.{}{name}",
        if let Some(name) = &pkg {
            format!(
                "{}.{}.",
                name.namespace.to_moonbit_ident(),
                name.name.to_moonbit_ident()
            )
        } else {
            String::new()
        }
    )
}

trait ToMoonBitIdent: ToOwned {
    fn to_moonbit_ident(&self) -> Self::Owned;
}

impl ToMoonBitIdent for str {
    fn to_moonbit_ident(&self) -> String {
        // Escape MoonBit keywords
        match self {
            "continue" | "for" | "match" | "if" | "pub" | "priv" | "readonly" | "break"
            | "raise" | "try" | "except" | "catch" | "else" | "enum" | "struct" | "type"
            | "trait" | "return" | "let" | "mut" | "while" | "loop" | "extern" | "with"
            | "throw" | "init" | "main" | "test" | "in" | "guard" | "typealias" | "const"
            | "method" | "move" | "do" | "static" | "final" => {
                format!("{self}_")
            }
            _ => self.to_snake_case(),
        }
    }
}

trait ToMoonBitTypeIdent: ToOwned {
    fn to_moonbit_type_ident(&self) -> Self::Owned;
}

impl ToMoonBitTypeIdent for str {
    fn to_moonbit_type_ident(&self) -> String {
        // Escape MoonBit builtin types
        match self.to_upper_camel_case().as_str() {
            type_name @ ("Bool" | "Byte" | "Int" | "Int64" | "UInt" | "UInt64" | "Float"
            | "Double" | "Error" | "Buffer" | "Bytes" | "Array" | "FixedArray"
            | "Map" | "String" | "Option" | "Result" | "Char" | "Json") => {
                format!("{type_name}_")
            }
            type_name => type_name.to_owned(),
        }
    }
}

fn generated_preamble(src: &mut Source, version: &str) {
    uwriteln!(src, "// Generated by `wit-bindgen` {version}.")
}

fn print_docs(src: &mut String, docs: &Docs) {
    if let Some(docs) = &docs.contents {
        let lines = docs
            .trim()
            .lines()
            .map(|line| format!("/// {line}"))
            .collect::<Vec<_>>()
            .join("\n");

        uwrite!(src, "{}", lines)
    }
}
