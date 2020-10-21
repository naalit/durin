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
            let m = durin::parse::Parser::new(&input).parse();
            let triple = inkwell::targets::TargetMachine::get_default_triple();
            inkwell::targets::Target::initialize_native(
                &inkwell::targets::InitializationConfig::default(),
            )
            .unwrap();
            let machine = inkwell::targets::Target::from_triple(&triple)
                .unwrap()
                .create_target_machine(
                    &triple,
                    inkwell::targets::TargetMachine::get_host_cpu_name()
                        .to_str()
                        .unwrap(),
                    inkwell::targets::TargetMachine::get_host_cpu_features()
                        .to_str()
                        .unwrap(),
                    inkwell::OptimizationLevel::None,
                    inkwell::targets::RelocMode::Default,
                    inkwell::targets::CodeModel::Default,
                )
                .unwrap();
            let cxt = inkwell::context::Context::create();
            let mut cxt = durin::backend::Cxt::new(&cxt, machine);
            m.codegen(&mut cxt);
            println!("{}", cxt.module.print_to_string().to_str().unwrap());
            cxt.module.verify().unwrap();
        }
    };
}

#[test]
fn test_basic() {
    let input = include_str!("basic.du");
    let m = durin::parse::Parser::new(input).parse();
    assert_eq!(input.trim(), m.emit().trim());
}

#[test]
fn test_range() {
    let input = include_str!("range.du");
    let m = durin::parse::Parser::new(input).parse();
    println!("{}", m.emit());
    // panic!("ah");
}

verify!(basic);
verify!(ssa);
