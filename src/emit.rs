use crate::ir::*;
use std::fmt::{self, Display, Write};

pub struct PrettyVal<'a>(&'a Module, Val, bool);
impl<'a> Display for PrettyVal<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let PrettyVal(m, v, force_write) = *self;
        if m.get(v).is_none() {
            return write!(f, "<None>");
        }
        if !force_write {
            if let Some(x) = &m.names[v.num()] {
                return write!(f, "{}", x);
            }
        }
        let x = match m.get(v).as_ref().unwrap() {
            Node::Const(c) => write!(f, "{}", c),
            Node::ExternFunType(params, r) => {
                write!(f, "extern fun(")?;
                let mut first = true;
                for (i, ty) in params.iter().enumerate() {
                    if !first {
                        write!(f, ", ")?;
                    }
                    first = false;
                    write!(f, "{}{}", m.param_name(v, i as u8), ty.pretty(m))?;
                }
                write!(f, ") -> {}", r.pretty(m))
            }
            Node::FunType(i) => {
                write!(f, "fun {}", i)
            }
            Node::ProdType(params) => {
                write!(f, "sig {{ ")?;
                let mut first = true;
                for (i, ty) in params.iter().enumerate() {
                    if !first {
                        write!(f, ", ")?;
                    }
                    first = false;
                    write!(f, "{}{}", m.param_name(v, i as u8), ty.pretty(m))?;
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
            Node::If(x) => {
                write!(f, "if {}", x.pretty(m))
            }
            Node::IfCase(i, x) => {
                write!(f, "ifcase {} {}", i, x.pretty(m))
            }
            Node::Ref(op) => match op {
                RefOp::RefNew(ty) => write!(f, "refnew {}", ty.pretty(m)),
                RefOp::RefGet(ptr) => write!(f, "refget {}", ptr.pretty(m)),
                RefOp::RefSet(ptr, val) => write!(f, "refset {} {}", ptr.pretty(m), val.pretty(m)),
            },
            Node::ExternCall(x) => {
                write!(f, "externcall {}", x.pretty(m))
            }
            Node::BinOp(op, a, b) => {
                write!(f, "({} {} {})", a.pretty(m), op, b.pretty(m))
            }
            // Node::Param(a, b) => write!(f, "{}.{}", a.pretty(m), b),
            _ => match &m.names[v.num()] {
                Some(x) => write!(f, "{}", x),
                None => write!(f, "%{}", v.num()),
            },
        };
        x
    }
}

impl Val {
    pub fn pretty(self, m: &Module) -> PrettyVal {
        PrettyVal(m, self, false)
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
        if name.len() == 1 && !self.uses(*name[0]).is_empty() {
            format!("{}: ", self.name_or(name[0].num()))
        } else if name.len() > 1 {
            format!("{}.{}: ", self.name_or(v.num()), pnum)
        } else {
            String::new()
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
                    Node::ExternFun(name, params, ret) => {
                        write!(buf, "extern fun {} (", name).unwrap();
                        let mut first = true;
                        for i in params {
                            if first {
                                first = false;
                            } else {
                                write!(buf, ", ").unwrap();
                            }
                            write!(buf, "{}", i.pretty(self)).unwrap()
                        }
                        writeln!(buf, "): {};", ret.pretty(self)).unwrap();
                    }
                    Node::RefTy(x) => {
                        writeln!(buf, "val {} = ref {};", self.name_or(num), x.pretty(self),)
                            .unwrap();
                    }
                    _ if !matches!(node, Node::Param(_, _)) && self.names[num].is_some() => {
                        writeln!(
                            buf,
                            "val {} = {};",
                            self.name_or(num),
                            PrettyVal(self, Val::from_num(num), true),
                        )
                        .unwrap();
                    }
                    _ => {
                        // Nothing, since constants and params are inlined
                    }
                },
                Slot::Redirect(v) => {
                    writeln!(buf, "val {} = {};", self.name_or(num), v.pretty(self),).unwrap()
                }
                _ => (),
            }
        }
        buf
    }
}
