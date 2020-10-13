use crate::ir::*;
use std::collections::HashSet;

pub trait Backend {
    fn define_fun(
        &mut self,
        m: &Module,
        val: Val,
        fun: Function,
        ty: FunType,
        blocks: Vec<(Val, Function)>,
    );
}

/// A messy, proof-of-concept backend generating an SSA-form dialect of Durin
#[derive(Default)]
pub struct SimpleSSA {
    pub body: String,
}
impl SimpleSSA {
    fn value(&mut self, m: &Module, v: Val) -> String {
        use std::fmt::Write;

        match m.get(v).as_ref().unwrap() {
            Node::Const(c) => format!("{}", c),
            Node::BinOp(op, a, b) => {
                let a = self.value(m, *a);
                let b = self.value(m, *b);
                let n = match &m.names[v.num()] {
                    Some(x) => format!("{}", x),
                    None => format!("%{}", v.num()),
                };
                write!(self.body, "  val {} = {} {} {}\n", n, a, op, b).unwrap();
                n
            }
            Node::Param(_, _) | Node::Fun(_) => match &m.names[v.num()] {
                Some(x) => format!("{}", x),
                None => format!("%{}", v.num()),
            },
            Node::FunType(_) => String::from("closure()"),
        }
    }
}
impl Backend for SimpleSSA {
    fn define_fun(
        &mut self,
        m: &Module,
        val: Val,
        fun: Function,
        ty: FunType,
        blocks: Vec<(Val, Function)>,
    ) {
        use std::fmt::Write;

        self.body.push_str("fun ");
        self.body.push_str(&m.name_or(val.num()));
        self.body.push_str(" (");
        for (pnum, pty) in fun.params.iter().enumerate() {
            if pnum == fun.params.len() - 1 && ty == FunType::Returning {
                break;
            }
            let name = {
                let name: Vec<_> = m
                    .uses(val)
                    .iter()
                    .filter(|&&x| {
                        if let Some(Node::Param(_, i)) = m.get(x) {
                            *i as usize == pnum
                        } else {
                            false
                        }
                    })
                    .collect();
                if name.len() == 1 {
                    m.name_or(name[0].num())
                } else {
                    format!("{}.{}", m.name_or(val.num()), pnum)
                }
            };
            write!(
                self.body,
                "{}{} : {}",
                if pnum == 0 { "" } else { ", " },
                name,
                pty.pretty(m),
            )
            .unwrap();
        }
        let ret = match ty {
            FunType::Returning => {
                let pnum = fun.params.len() - 1;
                let &ret = m
                    .uses(val)
                    .iter()
                    .filter(|&&x| {
                        if let Some(Node::Param(_, i)) = m.get(x) {
                            *i as usize == pnum
                        } else {
                            false
                        }
                    })
                    .next()
                    .unwrap();
                let rty = if let Node::FunType(v) = m.get(fun.params[pnum]).unwrap() {
                    if v.len() == 1 {
                        format!("{}", v[0].pretty(m))
                    } else {
                        let mut s = String::new();
                        s.push('(');
                        let mut first = true;
                        for i in v {
                            if !first {
                                first = false;
                                write!(s, ", ").unwrap();
                            }
                            write!(s, "{}", i.pretty(m)).unwrap();
                        }
                        s.push(')');
                        s
                    }
                } else {
                    unreachable!()
                };
                write!(self.body, "): {}", rty).unwrap();
                Some(ret)
            }
            _ => {
                self.body.push(')');
                None
            }
        };

        self.body.push_str(" {\nentry:\n");
        let args: Vec<_> = fun.call_args.iter().map(|&v| self.value(m, v)).collect();
        if Some(fun.callee) == ret {
            write!(self.body, "  ret (").unwrap();
        } else if blocks.iter().any(|(v, _)| *v == fun.callee) {
            write!(self.body, "  jump {} (", fun.callee.pretty(m)).unwrap();
        } else {
            write!(self.body, "  call {} (", fun.callee.pretty(m)).unwrap();
        }
        for i in args {
            write!(self.body, "{}, ", i).unwrap();
        }
        self.body.pop();
        self.body.pop();
        self.body.push_str(")\n");

        for (val, block) in &blocks {
            let &val = val;
            write!(self.body, "{}(", val.pretty(m)).unwrap();
            for (pnum, pty) in block.params.iter().enumerate() {
                let name = {
                    let name: Vec<_> = m
                        .uses(val)
                        .iter()
                        .filter(|&&x| {
                            if let Some(Node::Param(_, i)) = m.get(x) {
                                *i as usize == pnum
                            } else {
                                false
                            }
                        })
                        .collect();
                    if name.len() == 1 {
                        m.name_or(name[0].num())
                    } else {
                        format!("{}.{}", m.name_or(val.num()), pnum)
                    }
                };
                write!(
                    self.body,
                    "{}{} : {}",
                    if pnum == 0 { "" } else { ", " },
                    name,
                    pty.pretty(m),
                )
                .unwrap();
            }
            self.body.push_str("):\n");

            let args: Vec<_> = block.call_args.iter().map(|&v| self.value(m, v)).collect();
            if Some(block.callee) == ret {
                write!(self.body, "  ret (").unwrap();
            } else if blocks.iter().any(|(v, _)| *v == block.callee) {
                write!(self.body, "  jump {} (", block.callee.pretty(m)).unwrap();
            } else {
                write!(self.body, "  call {} (", block.callee.pretty(m)).unwrap();
            }
            for i in args {
                write!(self.body, "{}, ", i).unwrap();
            }
            self.body.pop();
            self.body.pop();
            self.body.push_str(")\n");
        }

        self.body.push_str("}\n");
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum FunType {
    /// A function that isn't able to use the standard call stack.
    Tail,
    /// A function that can use the standard call stack.
    /// The last parameter is dropped, since it's the continuation.
    Returning,
    /// A basic block within the last Tail or Returning function.
    Block,
}

impl Module {
    pub fn codegen(&self, backend: &mut impl Backend) {
        let mut direct = HashSet::new();
        let mut changed = true;
        // Run to a fixed point to work with unordered definitions
        // TODO make it work for mutual recursion
        while changed {
            changed = false;

            for v in self.vals() {
                if direct.contains(&v) {
                    continue;
                }
                if let Node::Fun(Function {
                    params,
                    callee,
                    call_args,
                }) = self.get(v).unwrap()
                {
                    if let Node::FunType(_) = *self.get(*params.last().unwrap()).unwrap() {
                        let cont_n = params.len() as u8 - 1;
                        let &cont_p = self
                            .uses(v)
                            .iter()
                            .find(|&&x| *self.get(x).unwrap() == Node::Param(v, cont_n))
                            .expect("Continuation isn't used, I guess?");
                        let good = self.uses(cont_p).iter().all(|&u| {
                            // We can only replace the continuation with a call stack if the continuation is only called, not passed around.
                            match self.get(u).unwrap() {
                                Node::Fun(Function { callee, .. }) if *callee == cont_p => true,
                                _ => false,
                            }
                        }) && (direct.contains(callee)
                            || *callee == cont_p
                            // Allow calling functions that will become basic blocks, i.e. don't have continuations
                            || if let Node::Fun(Function { params, .. }) = self.get(*callee).unwrap() {
                                params.last().map_or(true, |t| if let Node::FunType(_) = *self.get(*t).unwrap() { false } else { true })
                            } else { false }
                            // Single recursion is fine
                            || *callee == v);

                        if good {
                            changed = true;
                            direct.insert(v);
                        }
                    }
                }
            }
        }

        let mut stack: Vec<_> = self.top_level().collect();
        let mut added: HashSet<_> = stack.iter().copied().collect();
        while let Some(v) = stack.pop() {
            if let Node::Fun(Function {
                params,
                callee,
                call_args,
            }) = self.get(v).unwrap()
            {
                let scope = self.scope(v);

                // Figure out which functions in `scope` can be basic blocks
                let blocks = scope
                    .into_iter()
                    .filter_map(|x| {
                        // We'll pass this separately
                        if x == v {
                            return None;
                        }
                        if let Some(Node::Fun(Function {
                            params,
                            callee,
                            call_args,
                        })) = self.get(x)
                        {
                            // A function is eligible for turning into a basic block if it doesn't take a continuation - it always branches to a known destination.
                            // That's approximated by not having any parameters with function types.
                            // Polymorphic parameters that *could* have function types don't count, because they can't be called.
                            if params
                                .iter()
                                .all(|&x| match *self.get(x).unwrap() {
                                    Node::FunType(_) => false,
                                    _ => true,
                                })
                                // It must also not be used as a first-class function (not passed around, just called)
                                // This is, in theory, an arbitrary LLVM-specific restriction
                                // In assembly and probably other IRs, basic blocks (labels) can be passed around just fine
                                && self.uses(x).iter().all(|u| match self.get(*u).unwrap() {
                                    Node::Fun(f) => f.call_args.iter().all(|a| *a != x),
                                    Node::Param(_, _) => true,
                                    _ => false,
                                })
                            {
                                Some((
                                    x,
                                    Function {
                                        params: params.clone(),
                                        callee: *callee,
                                        call_args: call_args.clone(),
                                    },
                                ))
                            } else {
                                if !added.contains(&x) {
                                    added.insert(x);
                                    stack.push(x);
                                }
                                None
                            }
                        } else {
                            // We'll materialize value nodes later
                            None
                        }
                    })
                    .collect();

                // Figure out if we can replace the continuation with a call stack
                let ty = if direct.contains(&v) {
                    FunType::Returning
                } else {
                    FunType::Tail
                };
                // if *self.get(*params.last().unwrap()).unwrap()
                //     == Node::Const(Constant::FunType)
                // {
                //     let cont_n = params.len() as u8 - 1;
                //     let &cont_p = self
                //         .uses(v)
                //         .iter()
                //         .find(|&&x| *self.get(x).unwrap() == Node::Param(v, cont_n))
                //         .expect("Continuation isn't used, I guess?");
                //     let good = self.uses(cont_p).iter().all(|&u| {
                //         // We can only replace the continuation with a call stack if the continuation is only called, not passed around.
                //         match self.get(u).unwrap() {
                //             Node::Fun(Function { callee, .. }) if *callee == cont_p => true,
                //             _ => false,
                //         }
                //     });
                //
                //     if good {
                //         FunType::Returning
                //     } else {
                //         FunType::Tail
                //     }
                // } else {
                //     FunType::Tail
                // };

                backend.define_fun(
                    self,
                    v,
                    Function {
                        params: params.clone(),
                        callee: *callee,
                        call_args: call_args.clone(),
                    },
                    ty,
                    blocks,
                )
            }
        }
    }
}
