use specs::ReadStorage;

use crate::ir::*;
use std::fmt::{self, Display, Write};

type PrettyData<'a> = (
    ReadStorage<'a, Slot>,
    ReadStorage<'a, Uses>,
    ReadStorage<'a, Name>,
);

pub struct PrettyVal<'a>(&'a PrettyData<'a>, Val, bool);
impl<'a> Display for PrettyVal<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let PrettyVal(data, val, force_write) = *self;
        let (slots, uses, names) = &data;
        if slots.node(val).is_none() {
            return write!(f, "<None>");
        }
        if !force_write {
            if let Some(x) = names.get(val) {
                return write!(f, "{}", **x);
            }
        }
        let x = match slots.node(val).as_ref().unwrap() {
            Node::Const(c) => write!(f, "{}", c),
            Node::ExternFunType(params, r) => {
                write!(f, "extern fun(")?;
                let mut first = true;
                for (i, ty) in params.iter().enumerate() {
                    if !first {
                        write!(f, ", ")?;
                    }
                    first = false;
                    write!(
                        f,
                        "{}{}",
                        val.param_name(i as u8, uses, slots, names),
                        ty.pretty(data)
                    )?;
                }
                write!(f, ") -> {}", r.pretty(data))
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
                    write!(f, "{}", p.pretty(data))?;
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
                    write!(f, "{}", i.pretty(data))?;
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
                    write!(f, "{}", i.pretty(data))?;
                }
                write!(f, " }} of {}", ty.pretty(data))
            }
            Node::Proj(ty, x, i) => {
                write!(f, "({}.{} of {})", x.pretty(data), i, ty.pretty(data))
            }
            Node::Inj(ty, i, v) => {
                write!(f, "({}:{} {})", ty.pretty(data), i, v.pretty(data))
            }
            Node::BinOp(op, signed, a, b) => {
                write!(
                    f,
                    "({} {}{} {})",
                    a.pretty(data),
                    if *signed { 's' } else { 'u' },
                    op,
                    b.pretty(data)
                )
            }
            Node::Unbox(x) => {
                write!(f, "unbox {}", x.pretty(data))
            }
            _ => match names.get(val) {
                Some(x) => write!(f, "{}", **x),
                None => write!(f, "%{}", val.id()),
            },
        };
        x
    }
}

pub trait ValPretty {
    fn pretty<'a>(self, data: &'a PrettyData<'a>) -> PrettyVal<'a>;

    fn param_name(
        self,
        pnum: u8,
        uses: &ReadStorage<Uses>,
        slots: &ReadStorage<Slot>,
        names: &ReadStorage<Name>,
    ) -> String;
}
impl ValPretty for Val {
    fn pretty<'a>(self, data: &'a PrettyData<'a>) -> PrettyVal<'a> {
        PrettyVal(data, self, false)
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
            name[0].name_or_num(names)
        } else if name.len() > 1 {
            format!("{}.{}", self.name_or_num(names), pnum)
        } else {
            String::new()
        }
    }
}

impl Module {
    pub fn emit(&self) -> String {
        let data = &(
            self.world.read_storage(),
            self.world.read_storage(),
            self.world.read_storage(),
        );
        let mut buf = String::new();
        for (val, node) in (&self.world.entities(), &self.world.read_storage::<Slot>()).join() {
            match node {
                Slot::Full(node) => match node {
                    Node::Fun(Function {
                        params,
                        callee,
                        call_args,
                    }) => {
                        write!(
                            buf,
                            "\nfun {} (",
                            val.name_or_num(&self.world.read_storage())
                        )
                        .unwrap();
                        for (pnum, pty) in params.iter().enumerate() {
                            let name = {
                                let name: Vec<_> = self
                                    .world
                                    .read_storage::<Uses>()
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
                                    name[0].name_or_num(&self.world.read_storage())
                                } else {
                                    format!(
                                        "{}.{}",
                                        val.name_or_num(&self.world.read_storage()),
                                        pnum
                                    )
                                }
                            };
                            write!(
                                buf,
                                "{}{} : {}",
                                if pnum == 0 { "" } else { ", " },
                                name,
                                pty.pretty(data)
                            )
                            .unwrap();
                        }
                        write!(buf, ") = ").unwrap();
                        match self.slots().node(*callee).unwrap() {
                            Node::If(x) => {
                                write!(buf, "if {}", x.pretty(data)).unwrap();
                                for v in call_args {
                                    write!(buf, " {}", v.pretty(data)).unwrap();
                                }
                            }
                            Node::IfCase(i, x) => {
                                write!(buf, "ifcase {} {}", i, x.pretty(data)).unwrap();
                                for v in call_args {
                                    write!(buf, " {}", v.pretty(data)).unwrap();
                                }
                            }
                            Node::Ref(ty, op) => {
                                match op {
                                    RefOp::RefNew => write!(buf, "refnew {}", ty.pretty(data)),
                                    RefOp::RefGet(ptr) => write!(
                                        buf,
                                        "refget {} {}",
                                        ty.pretty(data),
                                        ptr.pretty(data)
                                    ),
                                    RefOp::RefSet(ptr, val) => write!(
                                        buf,
                                        "refset {} {} {}",
                                        ty.pretty(data),
                                        ptr.pretty(data),
                                        val.pretty(data)
                                    ),
                                }
                                .unwrap();
                                for v in call_args {
                                    write!(buf, " {}", v.pretty(data)).unwrap();
                                }
                            }
                            Node::ExternCall(x, ret_ty) => {
                                write!(
                                    buf,
                                    "externcall {} {}",
                                    ret_ty.pretty(data),
                                    x.pretty(data)
                                )
                                .unwrap();
                                let mut first = true;
                                for v in call_args {
                                    if !first {
                                        write!(buf, ", ").unwrap();
                                    }
                                    first = false;
                                    write!(buf, "{}", v.pretty(data)).unwrap();
                                }
                                write!(buf, ")").unwrap();
                            }
                            _ => {
                                write!(buf, "call {} (", callee.pretty(data)).unwrap();
                                let mut first = true;
                                for v in call_args {
                                    if !first {
                                        write!(buf, ", ").unwrap();
                                    }
                                    first = false;
                                    write!(buf, "{}", v.pretty(data)).unwrap();
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
                            write!(buf, "{}", i.pretty(data)).unwrap()
                        }
                        writeln!(buf, "): {}", ret.pretty(data)).unwrap();
                    }
                    Node::RefTy(x) => {
                        writeln!(
                            buf,
                            "val {} = ref {}",
                            val.name_or_num(&self.world.read_storage()),
                            x.pretty(data)
                        )
                        .unwrap();
                    }
                    _ if !matches!(node, Node::Param(_, _)) && self.name(val).is_some() => {
                        writeln!(
                            buf,
                            "val {} = {}",
                            val.name_or_num(&self.world.read_storage()),
                            PrettyVal(data, val, true),
                        )
                        .unwrap();
                    }
                    _ => {
                        // Nothing, since constants and params are inlined
                    }
                },
                Slot::Redirect(v) => writeln!(
                    buf,
                    "val {} = {}",
                    val.name_or_num(&self.world.read_storage()),
                    v.pretty(data)
                )
                .unwrap(),
            }
        }
        buf
    }
}
