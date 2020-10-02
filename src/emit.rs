use crate::ir::*;
use std::fmt::{self, Display, Write};

pub struct PrettyVal<'a>(&'a Module, Val);
impl<'a> Display for PrettyVal<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let PrettyVal(m, v) = *self;
        match m.get(v).as_ref().unwrap() {
            Node::Const(c) => write!(f, "{}", c),
            // Node::Param(a, b) => write!(f, "{}.{}", a.pretty(m), b),
            _ => match &m.names[v.num()] {
                Some(x) => write!(f, "{}", x),
                None => write!(f, "%{}", v.num()),
            },
        }
    }
}

impl Val {
    pub fn pretty(self, m: &Module) -> PrettyVal {
        PrettyVal(m, self)
    }
}

impl Module {
    pub fn name_or(&self, n: usize) -> String {
        self.names[n].clone().unwrap_or_else(|| format!("%{}", n))
    }

    pub fn emit(&self) -> String {
        let mut buf = String::new();
        for (num, node) in self.nodes.iter().enumerate() {
            if let Some(node) = node.to_option() {
                match node {
                    Node::Fun(Function {
                        params,
                        callee,
                        call_args,
                    }) => {
                        write!(buf, "\nfun {} (", self.name_or(num)).unwrap();
                        for (pnum, pty) in params.iter().enumerate() {
                            let name = {
                                let name: Vec<_> = self.uses[num]
                                    .iter()
                                    .filter(|&&x| {
                                        if let Some(Node::Param(_, i)) = self.get(x) {
                                            *i as usize == pnum
                                        } else {
                                            false
                                        }
                                    })
                                    .collect();
                                if name.len() == 1 {
                                    self.name_or(name[0].num())
                                } else {
                                    format!("{}.{}", self.name_or(num), pnum)
                                }
                            };
                            write!(
                                buf,
                                "{}{} : {}",
                                if pnum == 0 { "" } else { ", " },
                                name,
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
                            "val {} = ({} {} {});",
                            self.name_or(num),
                            a.pretty(self),
                            op,
                            b.pretty(self)
                        )
                        .unwrap();
                    }
                }
            }
        }
        buf
    }
}
