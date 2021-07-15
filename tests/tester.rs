/// Creates a test asserting that "tests/$name.du" produces LLVM that passes verification
macro_rules! verify {
    ($name:ident) => {
        #[test]
        fn $name() {
            let input = {
                use std::fs::*;
                use std::io::*;
                let path = format!("tests/{}.du", stringify!($name));
                let mut file = File::open(path).unwrap();
                let mut buf = String::new();
                file.read_to_string(&mut buf).unwrap();
                buf
            };
            let mut m = durin::parse::Parser::new(&input).parse();
            let backend = durin::backend::Backend::native();
            let l = backend.codegen_module(&mut m);
            println!("{}", l.print_to_string().to_str().unwrap());
            l.verify().unwrap();
        }
    };
}
macro_rules! run {
    ($name:ident) => {
        #[test]
        fn $name() {
            let input = {
                use std::fs::*;
                use std::io::*;
                let path = format!("tests/{}.du", stringify!($name));
                let mut file = File::open(path).unwrap();
                let mut buf = String::new();
                file.read_to_string(&mut buf).unwrap();
                buf
            };
            run_file(stringify!($name), &input)
        }
    };
}

/// For the generated code to call
#[no_mangle]
extern "C" fn print_i32(i: i32) {
    println!("{}", i);
}
extern "C" {
    pub fn malloc(i: usize) -> *const i8;
}

fn run_file(file: &str, source: &str) {
    let mut m = durin::parse::Parser::new(source).parse();
    let path = format!("{}/test-{}.out", env!("OUT_DIR"), file);
    let path: &std::path::Path = path.as_ref();
    m.compile_and_link(path, false).unwrap();
    assert!(std::process::Command::new(path).status().unwrap().success());
}

#[test]
fn basic() {
    let input = include_str!("basic.du");
    let mut m = durin::parse::Parser::new(input).parse();
    // assert_eq!(input.trim(), m.emit().trim());

    let backend = durin::backend::Backend::native();
    let l = backend.codegen_module(&mut m);
    let s = l.print_to_string();
    let s = s.to_str().unwrap();
    println!("{}", s);
    l.verify().unwrap();
    assert!(
        s.contains("define tailcc i32 @f("),
        "f should use the LLVM stack!"
    );
}

// #[test]
// fn test_range() {
//     let input = include_str!("range.du");
//     let m = durin::parse::Parser::new(input).parse();
//     println!("{}", m.emit());
//     // panic!("ah");
// }

run!(unknown_int);

verify!(ssa);
verify!(closures);
verify!(pi);
verify!(adt);
verify!(sigma);
verify!(ifs);
verify!(blocks);
verify!(dec);
verify!(stuff);
verify!(refs);
verify!(range);
