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
            run_file(&input)
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

fn run_file(source: &str) {
    let mut m = durin::parse::Parser::new(source).parse();

    let backend = durin::backend::Backend::native();
    let l = backend.codegen_module(&mut m);
    let s = l.print_to_string();
    let s = s.to_str().unwrap();
    println!("{}", s);
    l.verify().unwrap();

    // The main function is tailcc, so generate a ccc wrapper function which just calls it
    let cxt = &backend.cxt;
    let main_fun = l.get_function("main").expect("No main function");
    let new_fun = l.add_function("$_start", cxt.void_type().fn_type(&[], false), None);
    {
        let b = cxt.create_builder();
        let bl = cxt.append_basic_block(new_fun, "entry");
        b.position_at_end(bl);

        // Direct style
        let call = b.build_call(main_fun, &[], "main_call");
        call.set_call_convention(durin::backend::TAILCC);
        call.set_tail_call(true);
        b.build_return(None);
    }

    // Then we JIT and run it
    let ee = l
        .create_jit_execution_engine(durin::inkwell::OptimizationLevel::None)
        .expect("Failed to create LLVM execution engine");
    if let Some(f) = l.get_function("malloc") {
        ee.add_global_mapping(&f, malloc as usize);
    }
    if let Some(f) = l.get_function("print_i32") {
        ee.add_global_mapping(&f, print_i32 as usize);
    }
    unsafe {
        ee.run_function(new_fun, &[]);
    }
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
