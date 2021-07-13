#[cfg(test)]
mod tests {
    use anyhow::Result;
    use std::{
        collections::HashMap,
        fs,
        path::{Path, PathBuf},
    };
    use wasmlink::{Linker, Module, Profile};
    use wasmtime_wasi::WasiCtxBuilder;

    fn module_path(name: &str) -> PathBuf {
        Path::new("modules/target/wasm32-wasi")
            .join(if cfg!(debug_assertions) {
                "debug"
            } else {
                "release"
            })
            .join(format!("{}.wasm", name))
    }

    fn witx_path(name: &str) -> PathBuf {
        let path = Path::new("modules/crates")
            .join(name)
            .join(format!("{}.witx", name));

        if path.is_file() {
            return path;
        }

        Path::new("../../tests").join(format!("{}.witx", name))
    }

    pub fn link(main: &str, imports: &[&str]) -> Result<Vec<u8>> {
        let main_bytes = fs::read(module_path(main))?;

        let main_module = Module::new("main", &main_bytes)?;

        let imports: HashMap<&str, Vec<u8>> = imports
            .iter()
            .map(|name| {
                fs::read(module_path(name))
                    .map(|bytes| (*name, bytes))
                    .map_err(Into::into)
            })
            .collect::<Result<HashMap<&str, Vec<u8>>>>()?;

        let import_modules: HashMap<&str, Module> = imports
            .iter()
            .map(|(name, bytes)| {
                Module::new(name, bytes).and_then(|mut m| {
                    let path = witx_path(name);
                    if path.is_file() {
                        m.read_interface(&path)?;
                    }
                    Ok((name.as_ref(), m))
                })
            })
            .collect::<Result<HashMap<_, _>>>()?;

        let linker = Linker::new(Profile::new());
        linker.link(&main_module, &import_modules)
    }

    pub fn run(module: &[u8]) -> Result<()> {
        use wasmtime::{Config, Engine, Module, Store};

        let mut config = Config::new();
        config.wasm_module_linking(true);
        config.wasm_multi_memory(true);

        let engine = Engine::new(&config)?;
        let mut linker = wasmtime::Linker::new(&engine);
        wasmtime_wasi::add_to_linker(&mut linker, |s| s)?;

        let module = Module::new(&engine, module)?;
        let mut store = Store::new(
            &engine,
            WasiCtxBuilder::new()
                .inherit_stdout()
                .inherit_stderr()
                .build(),
        );

        let instance = linker.instantiate(&mut store, &module)?;
        let start = instance.get_typed_func::<(), (), _>(&mut store, "_start")?;

        start.call(store, ())?;

        Ok(())
    }

    #[test]
    fn basic_types() -> Result<()> {
        run(&link("types-main", &["types"])?)
    }

    #[test]
    fn records() -> Result<()> {
        run(&link("records-main", &["records"])?)
    }

    #[test]
    fn flags() -> Result<()> {
        run(&link("flags-main", &["flags"])?)
    }

    #[test]
    fn lists() -> Result<()> {
        run(&link("lists-main", &["lists"])?)
    }

    #[test]
    fn variants() -> Result<()> {
        run(&link("variants-main", &["variants"])?)
    }

    #[test]
    fn resources() -> Result<()> {
        run(&link("resources-main", &["resources"])?)
    }

    #[test]
    fn resources_with_invalid_handle() -> Result<()> {
        let e = run(&link("resources-invalid-main", &["resources"])?).expect_err("should trap");

        assert!(e.to_string().contains("invalid_handle_trap"));

        Ok(())
    }
}
