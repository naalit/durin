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

#[test]
fn test_ssa() {
    let input = include_str!("basic.du");
    let m = durin::parse::Parser::new(input).parse();
    let mut b = durin::backend::SimpleSSA::default();
    m.codegen(&mut b);
    println!("{}", b.body);
    panic!("ah");
}

#[test]
fn test_ssa2() {
    let input = include_str!("ssa.du");
    let m = durin::parse::Parser::new(input).parse();
    let mut b = durin::backend::SimpleSSA::default();
    m.codegen(&mut b);
    println!("{}", b.body);
    panic!("ah");
}
