use smallvec::*;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Val(usize);
impl Val {
    pub fn num(self) -> usize {
        self.0
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Slot {
    Full(Node),
    Reserved,
    Open,
}
impl Slot {
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

#[derive(Default, Debug)]
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
        self.nodes.get(i.num()).map(|x| x.to_option()).flatten()
    }

    pub fn uses(&self, i: Val) -> &Vec<Val> {
        self.uses.get(i.num()).unwrap()
    }

    pub fn name(&self, i: Val) -> Option<&String> {
        self.names.get(i.num()).map(|x| x.as_ref()).flatten()
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
            fn has_param(m: &Module, x: Val, not: Val) -> bool {
                match m.get(x) {
                    None => true,
                    Some(Node::Param(p, _)) => *p != not,
                    Some(Node::Fun(_)) if x != not => false,
                    Some(n) => n.args().iter().any(|x| has_param(m, *x, not)),
                }
            }
            !has_param(self, *x, *x)
        })
    }

    pub fn vals<'a>(&'a self) -> impl Iterator<Item = Val> + 'a {
        (0..self.nodes.len())
            .map(|x| Val(x))
            .filter(move |x| self.get(*x).is_some())
    }

    /// Returns a list of everything that depends on `v`, transitively.
    pub fn scope(&self, v: Val) -> Vec<Val> {
        use std::collections::HashSet;

        let mut vec = vec![v];
        let mut ix = 0;
        let mut seen = HashSet::new();
        seen.insert(v);

        // Instead of using a stack, we use one vec that we go through in order, since we're going to return it too
        while let Some(&v) = vec.get(ix) {
            for &i in self.uses(v) {
                if !seen.contains(&i) {
                    seen.insert(i);
                    vec.push(i);
                }
            }
            ix += 1;
        }

        vec
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Node {
    Fun(Function),
    FunType(SmallVec<[Val; 4]>),
    /// The `Val` should point to a function
    Param(Val, u8),
    Const(Constant),
    BinOp(BinOp, Val, Val),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    Const(Constant),
    FunType(SmallVec<[Val; 4]>),
    Val(Val),
}
impl Ty {
    pub fn to_val(self, m: &mut Module) -> Val {
        match self {
            Ty::Const(c) => m.add(Node::Const(c), None),
            Ty::FunType(v) => m.add(Node::FunType(v), None),
            Ty::Val(v) => v,
        }
    }

    pub fn inline(self, m: &Module) -> Self {
        match self {
            Ty::Val(v) => match m.get(v).unwrap() {
                Node::Const(c) => Ty::Const(c.clone()),
                Node::FunType(v) => Ty::FunType(v.clone()),
                _ => Ty::Val(v),
            },
            x => x,
        }
    }
}
impl Node {
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
            Node::FunType(v) => v.clone(),
            Node::Param(f, _) => smallvec![*f],
            Node::BinOp(_, a, b) => smallvec![*a, *b],
            Node::Const(_) => SmallVec::new(),
        }
    }

    pub fn ty(&self, m: &Module) -> Ty {
        match self {
            Node::Fun(f) => Ty::FunType(f.params.as_slice().to_smallvec()),
            Node::FunType(_) => Ty::Const(Constant::TypeType),
            Node::Param(f, i) => {
                if let Node::Fun(f) = m.get(*f).unwrap() {
                    Ty::Val(f.params[*i as usize])
                } else {
                    panic!("non-function has no params")
                }
            }
            Node::Const(c) => match c {
                Constant::TypeType | Constant::IntType(_) => Ty::Const(Constant::TypeType),
                Constant::Int(w, _) => Ty::Const(Constant::IntType(*w)),
            },
            Node::BinOp(BinOp::IEq, _, _) => Ty::Const(Constant::IntType(Width::W1)),
            Node::BinOp(_, a, _) => m.get(*a).unwrap().clone().ty(m),
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
    IEq,
}

mod display {
    use super::*;

    impl std::fmt::Display for Constant {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            match self {
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
            }
        }
    }
}
