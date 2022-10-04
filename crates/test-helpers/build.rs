use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use wit_bindgen_core::{wit_parser::Interface, Direction, Generator};
use wit_component::ComponentEncoder;

fn main() {
    let out_dir = PathBuf::from(std::env::var_os("OUT_DIR").unwrap());

    let mut wasms = Vec::new();

    if cfg!(feature = "guest-rust") {
        let mut cmd = Command::new("cargo");
        cmd.arg("build")
            .current_dir("../test-rust-wasm")
            // TODO: this should go back to wasm32-wasi once we have an adapter
            // for snapshot 1 to a component
            .arg("--target=wasm32-unknown-unknown")
            .env("CARGO_TARGET_DIR", &out_dir)
            .env("CARGO_PROFILE_DEV_DEBUG", "1")
            .env("RUSTFLAGS", "-Clink-args=--export-table")
            .env_remove("CARGO_ENCODED_RUSTFLAGS");
        let status = cmd.status().unwrap();
        assert!(status.success());
        for file in out_dir
            .join("wasm32-unknown-unknown/debug")
            .read_dir()
            .unwrap()
        {
            let file = file.unwrap().path();
            if file.extension().and_then(|s| s.to_str()) != Some("wasm") {
                continue;
            }
            wasms.push((
                "rust",
                file.file_stem().unwrap().to_str().unwrap().to_string(),
                file.to_str().unwrap().to_string(),
            ));

            // The "invalid" test doesn't actually use the rust-guest macro
            // and doesn't put the custom sections in, so component translation
            // will fail.
            if file.file_stem().unwrap().to_str().unwrap() != "invalid" {
                // Validate that the module can be translated to a component, using
                // the component-type custom sections. We don't yet consume this component
                // anywhere.
                let module = fs::read(&file).expect("failed to read wasm file");
                ComponentEncoder::default()
                    .module(module.as_slice())
                    .expect("pull custom sections from module")
                    .validate(true)
                    .encode()
                    .expect("module can be translated to a component");
            }

            let dep_file = file.with_extension("d");
            let deps = fs::read_to_string(&dep_file).expect("failed to read dep file");
            for dep in deps
                .splitn(2, ":")
                .skip(1)
                .next()
                .unwrap()
                .split_whitespace()
            {
                println!("cargo:rerun-if-changed={}", dep);
            }
        }
        println!("cargo:rerun-if-changed=../test-rust-wasm/Cargo.toml");
    }

    if cfg!(feature = "guest-c") {
        for test_dir in fs::read_dir("../../tests/runtime").unwrap() {
            let test_dir = test_dir.unwrap().path();
            let c_impl = test_dir.join("wasm.c");
            if !c_impl.exists() {
                continue;
            }
            let imports = test_dir.join("imports.wit");
            let exports = test_dir.join("exports.wit");
            println!("cargo:rerun-if-changed={}", imports.display());
            println!("cargo:rerun-if-changed={}", exports.display());
            println!("cargo:rerun-if-changed={}", c_impl.display());

            let import = Interface::parse_file(&test_dir.join("imports.wit")).unwrap();
            let export = Interface::parse_file(&test_dir.join("exports.wit")).unwrap();
            let mut files = Default::default();
            // TODO: should combine this into one
            wit_bindgen_gen_guest_c::Opts::default()
                .build()
                .generate_all(&[import], &[], &mut files);
            wit_bindgen_gen_guest_c::Opts::default()
                .build()
                .generate_all(&[], &[export], &mut files);

            let out_dir = out_dir.join(format!(
                "c-{}",
                test_dir.file_name().unwrap().to_str().unwrap()
            ));
            drop(fs::remove_dir_all(&out_dir));
            fs::create_dir(&out_dir).unwrap();
            for (file, contents) in files.iter() {
                let dst = out_dir.join(file);
                fs::write(dst, contents).unwrap();
            }

            let path = PathBuf::from(env::var_os("WASI_SDK_PATH").expect(
                "point the `WASI_SDK_PATH` environment variable to the path of your wasi-sdk",
            ));
            let mut cmd = Command::new(path.join("bin/clang"));
            let out_wasm = out_dir.join("c.wasm");
            cmd.arg("--sysroot").arg(path.join("share/wasi-sysroot"));
            cmd.arg(c_impl)
                .arg(out_dir.join("imports.c"))
                .arg(out_dir.join("exports.c"))
                .arg("-I")
                .arg(&out_dir)
                .arg("-Wall")
                .arg("-Wextra")
                .arg("-Werror")
                .arg("-Wno-unused-parameter")
                .arg("-mexec-model=reactor")
                .arg("-g")
                .arg("-o")
                .arg(&out_wasm);
            println!("{:?}", cmd);
            let output = match cmd.output() {
                Ok(output) => output,
                Err(e) => panic!("failed to spawn compiler: {}", e),
            };

            if !output.status.success() {
                println!("status: {}", output.status);
                println!("stdout: ------------------------------------------");
                println!("{}", String::from_utf8_lossy(&output.stdout));
                println!("stderr: ------------------------------------------");
                println!("{}", String::from_utf8_lossy(&output.stderr));
                panic!("failed to compile");
            }

            wasms.push((
                "c",
                test_dir.file_stem().unwrap().to_str().unwrap().to_string(),
                out_wasm.to_str().unwrap().to_string(),
            ));
        }
    }

    if cfg!(feature = "guest-teavm-java") {
        for test_dir in fs::read_dir("../../tests/runtime").unwrap() {
            let test_dir = test_dir.unwrap().path();
            let java_impl = test_dir.join("wasm.java");
            if !java_impl.exists() {
                continue;
            }
            println!("cargo:rerun-if-changed={}", java_impl.display());

            let out_dir = out_dir.join(format!(
                "java-{}",
                test_dir.file_name().unwrap().to_str().unwrap()
            ));

            drop(fs::remove_dir_all(&out_dir));

            let java_dir = out_dir.join("src/main/java");

            for (wit, direction) in [
                ("imports.wit", Direction::Import),
                ("exports.wit", Direction::Export),
            ] {
                let path = test_dir.join(wit);
                println!("cargo:rerun-if-changed={}", path.display());
                let iface = Interface::parse_file(&path).unwrap();
                let package_dir = java_dir.join(&format!("wit_{}", iface.name));
                fs::create_dir_all(&package_dir).unwrap();
                let ifaces = &[iface];
                let mut files = Default::default();

                wit_bindgen_gen_guest_teavm_java::Opts::default()
                    .build()
                    .generate_all(
                        if direction == Direction::Import {
                            ifaces
                        } else {
                            &[]
                        },
                        if direction == Direction::Export {
                            ifaces
                        } else {
                            &[]
                        },
                        &mut files,
                    );

                for (file, contents) in files.iter() {
                    let dst = package_dir.join(file);
                    fs::write(dst, contents).unwrap();
                }
            }

            fs::copy(&java_impl, java_dir.join("wit_exports/ExportsImpl.java")).unwrap();
            fs::write(out_dir.join("pom.xml"), pom_xml(&["wit_exports.Exports"])).unwrap();
            fs::write(
                java_dir.join("Main.java"),
                include_bytes!("../gen-guest-teavm-java/tests/Main.java"),
            )
            .unwrap();

            let mut cmd = mvn();
            cmd.arg("prepare-package").current_dir(&out_dir);

            println!("{:?}", cmd);
            let output = match cmd.output() {
                Ok(output) => output,
                Err(e) => panic!("failed to run Maven: {}", e),
            };

            if !output.status.success() {
                println!("status: {}", output.status);
                println!("stdout: ------------------------------------------");
                println!("{}", String::from_utf8_lossy(&output.stdout));
                println!("stderr: ------------------------------------------");
                println!("{}", String::from_utf8_lossy(&output.stderr));
                panic!("failed to build");
            }

            wasms.push((
                "java",
                test_dir.file_stem().unwrap().to_str().unwrap().to_string(),
                out_dir
                    .join("target/generated/wasm/teavm-wasm/classes.wasm")
                    .to_str()
                    .unwrap()
                    .to_string(),
            ));
        }
    }

    let src = format!("const WASMS: &[(&str, &str, &str)] = &{:?};", wasms);
    std::fs::write(out_dir.join("wasms.rs"), src).unwrap();
}

#[cfg(unix)]
fn mvn() -> Command {
    Command::new("mvn")
}

#[cfg(windows)]
fn mvn() -> Command {
    let mut cmd = Command::new("cmd");
    cmd.args(&["/c", "mvn"]);
    cmd
}

fn pom_xml(classes_to_preserve: &[&str]) -> Vec<u8> {
    let xml = include_str!("../gen-guest-teavm-java/tests/pom.xml");
    let position = xml.find("<mainClass>").unwrap();
    let (before, after) = xml.split_at(position);
    let classes_to_preserve = classes_to_preserve
        .iter()
        .map(|&class| format!("<param>{class}</param>"))
        .collect::<Vec<_>>()
        .join("\n");

    format!(
        "{before}
         <classesToPreserve>
            {classes_to_preserve}
         </classesToPreserve>
         {after}"
    )
    .into_bytes()
}
