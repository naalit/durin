use std::env;
use std::path::*;
use std::process::*;

fn main() {
    #[cfg(feature = "llvm-13")]
    {
        if option_env!("LLVM_DIR").is_none() {
            panic!("Must define LLVM_DIR environment variable to the LLVM 13 build directory to use llvm-13 feature!")
        }
        if option_env!("LLVM_SYS_120_PREFIX").is_none() {
            panic!("LLVM_SYS_120_PREFIX environment variable should be defined the same as LLVM_DIR to enable linking with the proper LLVM version!")
        }
    }

    #[cfg(not(feature = "llvm-13"))]
    if option_env!("LLVM_SYS_120_PREFIX").is_some() && option_env!("LLVM_DIR").is_some() {
        panic!("You forgot to unset LLVM_SYS_120_PREFIX after disabling the llvm-13 feature. This will cause a linking error!
                If you want to use a custom LLVM prefix without LLVM 13, unset the LLVM_DIR environment variable.");
    }

    println!("cargo:rerun-if-changed=src/runtime");
    println!("cargo:rerun-if-changed=src/llvm");
    let out_dir = env::var("OUT_DIR").unwrap();

    let mut build = cc::Build::new();
    build.cpp(true).files(&[
        "src/llvm/main.cpp",
        "src/llvm/inliner.cpp",
        "src/llvm/tailerizer.cpp",
    ]);
    #[cfg(feature = "llvm-13")]
    {
        build
            .includes(&[
                concat!(env!("LLVM_DIR"), "/include"),
                concat!(env!("LLVM_DIR"), "/../llvm/include"),
            ])
            .define("LLVM_13", None);
    }
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
