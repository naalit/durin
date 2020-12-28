use crate::ir::*;
use std::fmt::{self, Display, Write};

pub struct PrettyVal<'a>(&'a Module, Val);
impl<'a> Display for PrettyVal<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let PrettyVal(m, v) = *self;
        if let None = m.get(v) {
            return write!(f, "<None>");
        }
        match m.get(v).as_ref().unwrap() {
            Node::Const(c) => write!(f, "{}", c),
            Node::FunType(params) => {
                write!(f, "fun(")?;
                let mut first = true;
                for (i, ty) in params.iter().enumerate() {
                    if !first {
                        write!(f, ", ")?;
                    }
                    first = false;
                    write!(f, "{}: {}", m.param_name(v, i as u8), ty.pretty(m))?;
                }
                write!(f, ")")
            }
            Node::ProdType(params) => {
                write!(f, "sig {{ ")?;
                let mut first = true;
                for (i, ty) in params.iter().enumerate() {
                    if !first {
                        write!(f, ", ")?;
                    }
                    first = false;
                    write!(f, "{}: {}", m.param_name(v, i as u8), ty.pretty(m))?;
                }
                write!(f, " }}")
            }
            Node::SumType(v) => {
                write!(f, "(")?;
                let mut first = true;
                for i in v {
                    if !first {
                        write!(f, " | ")?;
                    }
                    first = false;
                    write!(f, "{}", i.pretty(m))?;
                }
                write!(f, ")")
            }
            Node::Product(ty, v) => {
                write!(f, "struct {{ ")?;
                let mut first = true;
                for i in v {
                    if !first {
                        write!(f, ", ")?;
                    }
                    first = false;
                    write!(f, "{}", i.pretty(m))?;
                }
                write!(f, " }} :: {}", ty.pretty(m))
            }
            Node::Proj(x, i) => {
                write!(f, "({}.{})", x.pretty(m), i)
            }
            Node::Inj(t, i, v) => {
                write!(f, "({}:{} {})", t.pretty(m), i, v.pretty(m))
            }
            Node::IfCase(i, x) => {
                write!(f, "ifcase {} {}", i, x.pretty(m))
            }
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

    pub fn param_name(&self, v: Val, pnum: u8) -> String {
        let name: Vec<_> = self
            .uses(v)
            .iter()
            .filter(|&&x| {
                if let Some(Node::Param(_, i)) = self.get(x) {
                    *i == pnum
                } else {
                    false
                }
            })
            .collect();
        if name.len() == 1 {
            self.name_or(name[0].num())
        } else {
            format!("{}.{}", self.name_or(v.num()), pnum)
        }
    }

    pub fn emit(&self) -> String {
        let mut buf = String::new();
        for (num, node) in self.nodes.iter().enumerate() {
            match node {
                Slot::Full(node) => match node {
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
                    _ => {
                        // Nothing, since constants and params are inlined
                    }
                },
                Slot::Redirect(v) => writeln!(
                    buf,
                    "val {} = {};",
                    self.name_or(num),
                    self.name_or(v.num())
                )
                .unwrap(),
                _ => (),
            }
        }
        buf
    }
}
