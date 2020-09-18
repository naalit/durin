#[test]
fn test_parse() {
    let m = durin::parse::Parser::new(include_str!("basic.du")).parse();
    for (i, n) in m.nodes.iter().enumerate() {
        println!("%{} = {}", i, n.as_ref().unwrap());
    }
    // panic!("look right?");
}
