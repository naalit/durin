use specs::ReadStorage;

use crate::ir::*;
use std::fmt::{self, Display, Write};

pub struct PrettyVal<'a>(&'a Module, Val, bool);
impl<'a> Display for PrettyVal<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let PrettyVal(m, v, force_write) = *self;
        if m.slots().node(v).is_none() {
            return write!(f, "<None>");
        }
        if !force_write {
            if let Some(x) = m.name(v) {
                return write!(f, "{}", x);
            }
        }
        let x = match m.slots().node(v).as_ref().unwrap() {
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
                for p in params {
                    if !first {
                        write!(f, ", ")?;
                    }
                    first = false;
                    write!(f, "{}", p.pretty(m))?;
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
                write!(f, "{{ ")?;
                let mut first = true;
                for i in v {
                    if !first {
                        write!(f, ", ")?;
                    }
                    first = false;
                    write!(f, "{}", i.pretty(m))?;
                }
                write!(f, " }} of {}", ty.pretty(m))
            }
            Node::Proj(ty, x, i) => {
                write!(f, "({}.{} of {})", x.pretty(m), i, ty.pretty(m))
            }
            Node::Inj(t, i, v) => {
                write!(f, "({}:{} {})", t.pretty(m), i, v.pretty(m))
            }
            Node::BinOp(op, signed, a, b) => {
                write!(
                    f,
                    "({} {}{} {})",
                    a.pretty(m),
                    if *signed { 's' } else { 'u' },
                    op,
                    b.pretty(m)
                )
            }
            Node::Unbox(x) => {
                write!(f, "unbox {}", x.pretty(m))
            }
            _ => match m.name(v) {
                Some(x) => write!(f, "{}", x),
                None => write!(f, "%{}", v.id()),
            },
        };
        x
    }
}

pub trait ValPretty {
    fn pretty(self, m: &Module) -> PrettyVal;

    fn param_name(
        self,
        pnum: u8,
        uses: &ReadStorage<Uses>,
        slots: &ReadStorage<Slot>,
        names: &ReadStorage<Name>,
    ) -> String;
}
impl ValPretty for Val {
    fn pretty(self, m: &Module) -> PrettyVal {
        PrettyVal(m, self, false)
    }

    fn param_name(
        self,
        pnum: u8,
        uses: &ReadStorage<Uses>,
        slots: &ReadStorage<Slot>,
        names: &ReadStorage<Name>,
    ) -> String {
        let name: Vec<_> = uses
            .get(self)
            .unwrap()
            .iter()
            .filter(|&&x| {
                if let Some(Node::Param(_, i)) = slots.node(x) {
                    *i == pnum
                } else {
                    false
                }
            })
            .copied()
            .collect();
        if name.len() == 1 && !uses.get(name[0]).unwrap().is_empty() {
            format!("{}", name[0].name_or_num(names))
        } else if name.len() > 1 {
            format!("{}.{}", self.name_or_num(names), pnum)
        } else {
            String::new()
        }
    }
}

impl Module {
    pub fn name_or(&self, v: Val) -> String {
        self.name(v).unwrap_or_else(|| format!("%{}", v.id()))
    }

    pub fn param_name(&self, v: Val, pnum: u8) -> String {
        let name: Vec<_> = self
            .uses()
            .get(v)
            .unwrap()
            .iter()
            .filter(|&&x| {
                if let Some(Node::Param(_, i)) = self.slots().node(x) {
                    *i == pnum
                } else {
                    false
                }
            })
            .copied()
            .collect();
        if name.len() == 1 && !self.uses().get(name[0]).unwrap().is_empty() {
            format!("{}: ", self.name_or(name[0]))
        } else if name.len() > 1 {
            format!("{}.{}: ", self.name_or(v), pnum)
        } else {
            String::new()
        }
    }

    pub fn emit(&self) -> String {
        let mut buf = String::new();
        for (val, node) in (&self.world.entities(), &self.world.read_storage::<Slot>()).join() {
            match node {
                Slot::Full(node) => match node {
                    Node::Fun(Function {
                        params,
                        callee,
                        call_args,
                    }) => {
                        write!(buf, "\nfun {} (", self.name_or(val)).unwrap();
                        for (pnum, pty) in params.iter().enumerate() {
                            let name = {
                                let name: Vec<_> = self
                                    .uses()
                                    .get(val)
                                    .unwrap()
                                    .iter()
                                    .filter(|&&x| {
                                        if let Some(Node::Param(_, i)) = self.slots().node(x) {
                                            *i as usize == pnum
                                        } else {
                                            false
                                        }
                                    })
                                    .copied()
                                    .collect();
                                if name.len() == 1 {
                                    self.name_or(name[0])
                                } else {
                                    format!("{}.{}", self.name_or(val), pnum)
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
                        write!(buf, ") = ").unwrap();
                        match self.slots().node(*callee).unwrap() {
                            Node::If(x) => {
                                write!(buf, "if {}", x.pretty(self)).unwrap();
                                for v in call_args {
                                    write!(buf, " {}", v.pretty(self)).unwrap();
                                }
                            }
                            Node::IfCase(i, x) => {
                                write!(buf, "ifcase {} {}", i, x.pretty(self)).unwrap();
                                for v in call_args {
                                    write!(buf, " {}", v.pretty(self)).unwrap();
                                }
                            }
                            Node::Ref(ty, op) => {
                                match op {
                                    RefOp::RefNew => write!(buf, "refnew {}", ty.pretty(self)),
                                    RefOp::RefGet(ptr) => write!(
                                        buf,
                                        "refget {} {}",
                                        ty.pretty(self),
                                        ptr.pretty(self)
                                    ),
                                    RefOp::RefSet(ptr, val) => write!(
                                        buf,
                                        "refset {} {} {}",
                                        ty.pretty(self),
                                        ptr.pretty(self),
                                        val.pretty(self)
                                    ),
                                }
                                .unwrap();
                                for v in call_args {
                                    write!(buf, " {}", v.pretty(self)).unwrap();
                                }
                            }
                            Node::ExternCall(x, ret_ty) => {
                                write!(
                                    buf,
                                    "externcall {} {}",
                                    ret_ty.pretty(self),
                                    x.pretty(self)
                                )
                                .unwrap();
                                let mut first = true;
                                for v in call_args {
                                    if !first {
                                        write!(buf, ", ").unwrap();
                                    }
                                    first = false;
                                    write!(buf, "{}", v.pretty(self)).unwrap();
                                }
                                write!(buf, ")").unwrap();
                            }
                            _ => {
                                write!(buf, "call {} (", callee.pretty(self)).unwrap();
                                let mut first = true;
                                for v in call_args {
                                    if !first {
                                        write!(buf, ", ").unwrap();
                                    }
                                    first = false;
                                    write!(buf, "{}", v.pretty(self)).unwrap();
                                }
                                write!(buf, ")").unwrap();
                            }
                        }
                        writeln!(buf).unwrap();
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
                        writeln!(buf, "): {}", ret.pretty(self)).unwrap();
                    }
                    Node::RefTy(x) => {
                        writeln!(buf, "val {} = ref {}", self.name_or(val), x.pretty(self),)
                            .unwrap();
                    }
                    _ if !matches!(node, Node::Param(_, _)) && self.name(val).is_some() => {
                        writeln!(
                            buf,
                            "val {} = {}",
                            self.name_or(val),
                            PrettyVal(self, val, true),
                        )
                        .unwrap();
                    }
                    _ => {
                        // Nothing, since constants and params are inlined
                    }
                },
                Slot::Redirect(v) => {
                    writeln!(buf, "val {} = {}", self.name_or(val), v.pretty(self),).unwrap()
                }
            }
        }
        buf
    }
}
