use std::env;
use std::path::*;
use std::process::*;

fn main() {
    println!("cargo:rerun-if-changed=src/runtime");
    println!("cargo:rerun-if-changed=src/llvm");
    let out_dir = env::var("OUT_DIR").unwrap();

    let mut build = cc::Build::new();
    build.cpp(true).files(&[
        "src/llvm/main.cpp",
        "src/llvm/inliner.cpp",
        "src/llvm/tailerizer.cpp",
    ]);
    build.warnings(false).compile("durin-llvm");

    let mut out_file = PathBuf::from(out_dir.clone());
    out_file.push("prelude.bc");
    if !Command::new("llvm-as")
        .args(&["src/runtime/prelude.ll", "-o"])
        .arg(out_file)
        .status()
        .unwrap()
        .success()
    {
        panic!("Failed to assemble prelude.ll");
    }

    let mut out_file = PathBuf::from(out_dir);
    out_file.push("runtime.bc");
    if !Command::new("clang")
        .args(&["src/runtime/runtime.c", "-c", "-emit-llvm", "-g", "-o"])
        .arg(out_file)
        .status()
        .unwrap()
        .success()
    {
        panic!("Failed to compile runtime.c");
    }
}
