use crate::ir::*;
use std::fmt::{self, Display, Write};

struct PrettyVal<'a>(&'a Module, Val);
impl<'a> Display for PrettyVal<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let PrettyVal(m, v) = *self;
        match m.get(v).as_ref().unwrap() {
            Node::Const(c) => write!(f, "{}", c),
            Node::Param(a, b) => write!(f, "{}.{}", a.pretty(m), b),
            _ => match &m.names[v.num()] {
                Some(x) => write!(f, "{}", x),
                None => write!(f, "%{}", v.num()),
            },
        }
    }
}

impl Val {
    fn pretty(self, m: &Module) -> PrettyVal {
        PrettyVal(m, self)
    }
}

impl Module {
    fn name_or(&self, n: usize) -> String {
        self.names[n].clone().unwrap_or_else(|| format!("%{}", n))
    }

    pub fn emit(&self) -> String {
        let mut buf = String::new();
        for (num, node) in self.nodes.iter().enumerate() {
            match node.as_ref().unwrap() {
                Node::Fun(Function {
                    params,
                    callee,
                    call_args,
                }) => {
                    write!(buf, "\nfun {} (", self.name_or(num)).unwrap();
                    for (pnum, pty) in params.iter().enumerate() {
                        write!(
                            buf,
                            "{}{}.{} : {}",
                            if pnum == 0 { "" } else { ", " },
                            self.name_or(num),
                            pnum,
                            pty.pretty(self)
                        )
                        .unwrap();
                    }
                    write!(buf, ") = {}", callee.pretty(self)).unwrap();
                    for v in call_args {
                        write!(buf, " {}", v.pretty(self)).unwrap();
                    }
                    writeln!(buf, ";").unwrap();
                }
                Node::Param(_, _) | Node::Const(_) => {
                    // Nothing, since constants and params are inlined
                }
                Node::BinOp(op, a, b) => {
                    writeln!(
                        buf,
                        "val {} = {} {} {};",
                        self.name_or(num),
                        op,
                        a.pretty(self),
                        b.pretty(self)
                    )
                    .unwrap();
                }
            }
        }
        buf
    }
}
