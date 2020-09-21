#[test]
fn test_parse() {
    let input = include_str!("basic.du");
    let m = durin::parse::Parser::new(input).parse();
    assert_eq!(input.trim(), m.emit().trim());
}

#[test]
fn test_range() {
    let input = include_str!("range.du");
    let m = durin::parse::Parser::new(input).parse();
    println!("{}", m.emit());
    panic!("ah");
}
