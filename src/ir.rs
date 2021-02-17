use smallvec::*;
use std::collections::{HashMap, HashSet};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Val(usize);
impl Val {
    pub fn unredirect(self, m: &Module) -> Val {
        match m.nodes.get(self.num()) {
            Some(Slot::Redirect(x)) => x.unredirect(m),
            _ => self,
        }
    }

    pub fn get(self, m: &Module) -> &Node {
        m.get(self).unwrap()
    }

    pub fn num(self) -> usize {
        self.0
    }

    pub(crate) fn from_num(n: usize) -> Self {
        Val(n)
    }

    /// An invalid value that can't have a Node associated with it
    pub const INVALID: Self = Val(usize::MAX);
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Slot {
    Full(Node),
    Redirect(Val),
    Reserved,
    Open,
}
impl Slot {
    pub fn to_option_mut(&mut self) -> Option<&mut Node> {
        if let Slot::Full(n) = self {
            Some(n)
        } else {
            None
        }
    }

    pub fn to_option(&self) -> Option<&Node> {
        if let Slot::Full(n) = self {
            Some(n)
        } else {
            None
        }
    }

    pub fn into_option(self) -> Option<Node> {
        if let Slot::Full(n) = self {
            Some(n)
        } else {
            None
        }
    }
}

#[derive(Default, Debug, Clone, Eq, PartialEq)]
pub struct Module {
    pub nodes: Vec<Slot>,
    pub uses: Vec<Vec<Val>>,
    pub names: Vec<Option<String>>,
}
impl Module {
    /// Removes a node from the module. Panics if that node is used by anything.
    pub fn remove(&mut self, i: Val) -> Option<Node> {
        if !self.uses[i.num()].is_empty() {
            panic!("Error: cannot delete node with uses!")
        }
        self.uses[i.num()] = Vec::new();
        self.names[i.num()] = None;
        // Why isn't there a Vec::replace()?
        std::mem::replace(&mut self.nodes[i.num()], Slot::Open).into_option()
    }

    pub fn get(&self, i: Val) -> Option<&Node> {
        let mut i = i;
        loop {
            match self.nodes.get(i.num())? {
                Slot::Full(x) => break Some(x),
                Slot::Redirect(v) => i = *v,
                Slot::Reserved | Slot::Open => break None,
            }
        }
    }

    pub fn get_mut(&mut self, i: Val) -> Option<&mut Node> {
        let mut i = i;
        loop {
            match self.nodes.get(i.num())? {
                Slot::Full(_) => {
                    break self
                        .nodes
                        .get_mut(i.num())
                        .map(|x| x.to_option_mut())
                        .unwrap()
                }
                Slot::Redirect(v) => i = *v,
                Slot::Reserved | Slot::Open => break None,
            }
        }
    }

    pub fn uses(&self, i: Val) -> &Vec<Val> {
        self.uses.get(i.num()).unwrap()
    }

    pub fn name(&self, i: Val) -> Option<&String> {
        self.names.get(i.num()).map(|x| x.as_ref()).flatten()
    }

    pub fn set_name(&mut self, i: Val, n: Option<String>) {
        self.names[i.num()] = n;
    }

    // TODO deduplicate constants, or just everything (implicit CSE)
    pub fn add(&mut self, x: Node, n: Option<String>) -> Val {
        let args = x.args();
        let v = Val(self.nodes.len());
        self.nodes.push(Slot::Full(x));
        self.uses.push(Vec::new());
        self.names.push(n);

        // Add uses for the things the new value uses
        for i in args {
            self.uses[i.num()].push(v);
        }

        v
    }

    /// Reserves space for a value. Used for forward references.
    /// Fill the value later with `replace()`.
    pub fn reserve(&mut self, n: Option<String>) -> Val {
        let v = Val(self.nodes.len());
        self.nodes.push(Slot::Reserved);
        self.uses.push(Vec::new());
        self.names.push(n);
        v
    }

    pub fn redirect(&mut self, from: Val, to: Val) {
        self.nodes[from.num()] = Slot::Redirect(to);
        // If we use redirect() to give this node a name, transfer that over
        if self.name(to).is_none() {
            if let Some(name) = self.name(from) {
                self.names[to.num()] = Some(name.clone());
            }
        }
    }

    pub fn replace(&mut self, v: Val, x: Node) {
        // Since there aren't usually many arguments, it's simplest to just remove old uses and add new ones
        let old_args = self.nodes[v.num()]
            .to_option()
            .map_or(SmallVec::new(), |x| x.args());
        let new_args = x.args();

        for i in old_args {
            let u = &mut self.uses[i.num()];
            let i = u.iter().position(|&x| x == v).unwrap();
            u.swap_remove(i);
        }
        for i in new_args {
            self.uses[i.num()].push(v);
        }

        self.nodes[v.num()] = Slot::Full(x);
    }

    pub fn top_level<'a>(&'a self) -> impl Iterator<Item = Val> + 'a {
        (0..self.nodes.len()).map(|x| Val(x)).filter(move |x| {
            // A node is top-level if it:
            // 1. is a function (and not a redirect)
            if !matches!(self.nodes.get(x.num()), Some(Slot::Full(Node::Fun(_)))) {
                return false;
            }

            // 2. doesn't use parameters from other functions at runtime
            fn has_param(m: &Module, x: Val, not: &mut HashSet<Val>) -> bool {
                let x = x.unredirect(m);
                match m.get(x) {
                    None => unreachable!(),
                    Some(Node::Param(p, _)) => {
                        !not.contains(p)
                            && if let Some(Node::Fun(_)) = m.get(*p) {
                                true
                            } else {
                                false
                            }
                    }
                    Some(Node::Fun(_)) | Some(Node::FunType(_)) | Some(Node::ProdType(_)) => {
                        if !not.contains(&x) {
                            // If it calls another function, that function can use its own parameters
                            not.insert(x);
                            let b = m
                                .get(x)
                                .unwrap()
                                .runtime_args()
                                .iter()
                                .any(|x| has_param(m, *x, not)); //has_param(m, x, not);
                            not.remove(&x);
                            b
                        } else {
                            false
                        }
                    }
                    Some(n) => n.runtime_args().iter().any(|x| has_param(m, *x, not)),
                }
            }
            !has_param(self, *x, &mut std::iter::once(*x).collect())
        })
    }

    pub fn vals<'a>(&'a self) -> impl Iterator<Item = Val> + 'a {
        (0..self.nodes.len())
            .map(|x| Val(x))
            .filter(move |x| self.get(*x).is_some())
    }

    /// Returns a list of all foreign parameters this node depends on, with their types.
    pub fn env(&self, v: Val) -> Vec<(Val, Val)> {
        fn go(m: &Module, v: Val, seen: &mut HashSet<Val>, acc: &mut HashSet<(Val, Val)>) {
            let v = v.unredirect(m);
            match m.get(v).unwrap() {
                Node::Param(f, i) => {
                    if seen.contains(f) {
                    } else {
                        match m.get(*f).unwrap() {
                            Node::Fun(Function { params, .. }) => {
                                acc.insert((v, params[*i as usize]));
                            }
                            // Parameters of pi or sigma types don't count
                            Node::FunType(_) | Node::ProdType(_) => (),
                            _ => unreachable!(),
                        }
                    }
                }
                n @ Node::Fun(_) => {
                    if !seen.contains(&v) {
                        seen.insert(v);
                        for i in n.runtime_args() {
                            go(m, i, seen, acc)
                        }
                        seen.remove(&v);
                    }
                }
                n => {
                    for i in n.runtime_args() {
                        go(m, i, seen, acc)
                    }
                }
            }
        }
        let mut acc = HashSet::new();
        go(self, v, &mut HashSet::new(), &mut acc);
        acc.into_iter().collect()
    }

    /// Returns all functions that `v` depends on the parameters of, and so must be within, recursively.
    pub fn dependencies(&self, v: Val) -> Vec<Val> {
        fn go(m: &Module, v: Val, seen: &mut HashSet<Val>, acc: &mut HashSet<Val>) {
            let v = v.unredirect(m);
            match m.get(v).unwrap() {
                Node::Param(f, _) => {
                    if seen.contains(f) {
                    } else {
                        match m.get(*f).unwrap() {
                            Node::Fun(Function { .. }) => {
                                acc.insert(*f);
                            }
                            // Parameters of pi or sigma types don't count
                            Node::FunType(_) | Node::ProdType(_) => (),
                            _ => unreachable!(),
                        }
                    }
                }
                n @ Node::Fun(_) => {
                    if !seen.contains(&v) {
                        seen.insert(v);
                        for i in n.runtime_args() {
                            go(m, i, seen, acc)
                        }
                        seen.remove(&v);
                    }
                }
                n => {
                    for i in n.runtime_args() {
                        go(m, i, seen, acc)
                    }
                }
            }
        }
        let mut acc = HashSet::new();
        go(self, v, &mut HashSet::new(), &mut acc);
        acc.into_iter().collect()
    }

    /// Returns the scope of each function in this module, i.e. for each function, everything that must be nested directly within it.
    pub fn top_level_scopes(&self) -> HashMap<Val, Vec<Val>> {
        let mut top_level = Vec::new();
        let mut scopes: HashMap<Val, Vec<Val>> = HashMap::new();
        for i in 0..self.nodes.len() {
            let i = Val(i);
            // Skip redirects for this
            if i != i.unredirect(self) {
                continue;
            }
            // Also skip anything but functions
            if !matches!(self.get(i), Some(Node::Fun(_))) {
                continue;
            }

            let deps = self.dependencies(i);
            if deps.is_empty() {
                top_level.push(i);
            } else {
                for d in deps {
                    scopes.entry(d).or_insert_with(Vec::new).push(i);
                }
            }
        }
        // top_level
        //     .into_iter()
        //     .map(|x| (x, scopes.remove(&x).unwrap_or_else(Vec::new)))
        //     .collect()
        scopes
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Node {
    Fun(Function),
    FunType(SmallVec<[Val; 4]>),
    ExternFun(String, SmallVec<[Val; 3]>, Val),
    /// Extern functions have a return type
    ExternFunType(SmallVec<[Val; 3]>, Val),
    ProdType(SmallVec<[Val; 4]>),
    SumType(SmallVec<[Val; 4]>),
    /// IfCase(tag, x); then and else are passed to it as arguments
    IfCase(usize, Val),
    ExternCall(Val),
    If(Val),
    /// Projecting a numbered member of a product type
    Proj(Val, usize),
    /// Injecting a numbered member of a sum type (the type is the first argument)
    Inj(Val, usize, Val),
    Product(Val, SmallVec<[Val; 3]>),
    /// The `Val` should point to a function
    Param(Val, u8),
    Const(Constant),
    BinOp(BinOp, Val, Val),
}
impl Node {
    /// Arguments that, *if they're only known at runtime*, exist in the generated LLVM IR.
    /// So, not types of things.
    fn runtime_args(&self) -> SmallVec<[Val; 4]> {
        match self {
            Node::Fun(Function {
                callee, call_args, ..
            }) => call_args
                .iter()
                .copied()
                .chain(std::iter::once(*callee))
                .collect(),
            Node::Product(_, v) => v.to_smallvec(),
            Node::ProdType(v) | Node::SumType(v) => v.clone(),
            Node::BinOp(_, a, b) => smallvec![*a, *b],
            Node::IfCase(_, x)
            | Node::Proj(x, _)
            | Node::Inj(_, _, x)
            | Node::If(x)
            | Node::ExternCall(x) => {
                smallvec![*x]
            }
            // We don't need to know parameter types at runtime
            Node::FunType(_) => SmallVec::new(),
            Node::ExternFun(_, _, _) | Node::ExternFunType(_, _) => SmallVec::new(),
            Node::Const(_) => SmallVec::new(),
            // `f` not being known at runtime doesn't really make sense
            Node::Param(_f, _) => SmallVec::new(),
        }
    }

    pub fn args(&self) -> SmallVec<[Val; 4]> {
        match self {
            Node::Fun(Function {
                params,
                callee,
                call_args,
            }) => params
                .iter()
                .chain(call_args.iter())
                .copied()
                .chain(std::iter::once(*callee))
                .collect(),
            Node::Product(ty, v) => v.iter().copied().chain(std::iter::once(*ty)).collect(),
            Node::FunType(v) | Node::ProdType(v) | Node::SumType(v) => v.clone(),
            Node::ExternFun(_, v, r) | Node::ExternFunType(v, r) => {
                v.iter().copied().chain(std::iter::once(*r)).collect()
            }
            Node::Param(f, _) => smallvec![*f],
            Node::BinOp(_, a, b) | Node::Inj(a, _, b) => smallvec![*a, *b],
            Node::Const(_) => SmallVec::new(),
            Node::IfCase(_, x) | Node::Proj(x, _) | Node::If(x) | Node::ExternCall(x) => {
                smallvec![*x]
            }
        }
    }

    pub fn ty(&self, m: &mut Module) -> Val {
        match self {
            Node::Fun(f) => m.add(Node::FunType(f.params.as_slice().to_smallvec()), None),
            Node::ExternFun(_, p, r) => m.add(Node::ExternFunType(p.clone(), *r), None),
            Node::ExternCall(t) => match t.get(m).clone().ty(m).get(m) {
                Node::ExternFunType(p, r) => {
                    let mut p = p.as_slice().to_smallvec();
                    let &r = r;
                    let cont = m.add(Node::FunType(smallvec![r]), None);
                    p.push(cont);
                    m.add(Node::FunType(p), None)
                }
                _ => unreachable!(),
            },
            Node::FunType(_) | Node::ProdType(_) | Node::SumType(_) | Node::ExternFunType(_, _) => {
                m.add(Node::Const(Constant::TypeType), None)
            }
            Node::Product(ty, _) => *ty,
            Node::Param(f, i) => {
                if let Node::Fun(f) = m.get(*f).unwrap() {
                    f.params[*i as usize]
                } else {
                    panic!("non-function has no params")
                }
            }
            Node::Const(c) => match c {
                Constant::TypeType | Constant::IntType(_) => {
                    m.add(Node::Const(Constant::TypeType), None)
                }
                Constant::Int(w, _) => m.add(Node::Const(Constant::IntType(*w)), None),
                Constant::Stop | Constant::Unreachable => {
                    m.add(Node::FunType(SmallVec::new()), None)
                }
            },
            Node::BinOp(BinOp::IEq, _, _) => m.add(Node::Const(Constant::IntType(Width::W1)), None),
            Node::BinOp(_, a, _) => a.get(m).clone().ty(m),
            Node::If(_) => {
                let fty = m.add(Node::FunType(smallvec![]), None);
                // Takes `then` and `else` blocks as arguments
                m.add(Node::FunType(smallvec![fty, fty]), None)
            }
            Node::IfCase(i, x) => {
                let arg = match x.get(m).clone().ty(m).get(m) {
                    Node::SumType(v) => v[*i],
                    _ => unreachable!(),
                };
                let fone = m.add(Node::FunType(smallvec![arg]), None);
                let ftwo = m.add(Node::FunType(smallvec![]), None);
                m.add(Node::FunType(smallvec![fone, ftwo]), None)
            }
            Node::Proj(x, i) => match x.get(m).clone().ty(m).get(m) {
                Node::ProdType(v) => v[*i],
                _ => unreachable!(),
            },
            Node::Inj(t, _, _) => *t,
        }
    }
}

/// A function body is just a call
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Function {
    /// The parameter types
    pub params: SmallVec<[Val; 3]>,
    pub callee: Val,
    pub call_args: SmallVec<[Val; 3]>,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Width {
    W1,
    W8,
    W16,
    W32,
    W64,
}
impl Width {
    pub fn bits(self) -> u32 {
        match self {
            Width::W1 => 1,
            Width::W8 => 8,
            Width::W16 => 16,
            Width::W32 => 32,
            Width::W64 => 64,
        }
    }
}

/// Types are generally constants
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum Constant {
    Stop,
    Unreachable,
    TypeType,
    IntType(Width),
    Int(Width, i64),
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum BinOp {
    IAdd,
    ISub,
    IMul,
    IDiv,
    IExp,
    IAnd,
    IOr,
    IXor,
    IShl,
    IShr,
    IEq,
    INEq,
    IGt,
    ILt,
    IGeq,
    ILeq,
}

mod display {
    use super::*;

    impl std::fmt::Display for Constant {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            match self {
                Constant::Unreachable => write!(f, "unreachable"),
                Constant::Stop => write!(f, "stop"),
                Constant::TypeType => write!(f, "Type"),
                Constant::IntType(w) => write!(f, "I{}", w),
                Constant::Int(w, i) => write!(f, "{}i{}", i, w),
            }
        }
    }
    impl std::fmt::Display for Width {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            self.bits().fmt(f)
        }
    }
    impl std::fmt::Display for BinOp {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            match self {
                BinOp::IEq => write!(f, "=="),
                BinOp::IAdd => write!(f, "+"),
                BinOp::ISub => write!(f, "-"),
                BinOp::IMul => write!(f, "*"),
                BinOp::IDiv => write!(f, "/"),
                BinOp::IExp => write!(f, "**"),
                BinOp::IAnd => write!(f, "&"),
                BinOp::IOr => write!(f, "|"),
                BinOp::IXor => write!(f, "^"),
                BinOp::IShl => write!(f, "<<"),
                BinOp::IShr => write!(f, ">>"),
                BinOp::INEq => write!(f, "!="),
                BinOp::IGt => write!(f, ">"),
                BinOp::ILt => write!(f, "<"),
                BinOp::IGeq => write!(f, ">="),
                BinOp::ILeq => write!(f, "<="),
            }
        }
    }
}
