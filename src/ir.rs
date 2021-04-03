use smallvec::*;
pub use specs::prelude::{Join, World, WorldExt};
use specs::{prelude::*, Component};
use std::collections::{HashMap, HashSet};

pub type Val = Entity;

pub trait ValExt {
    fn get<'a>(self, slots: &'a ReadStorage<Slot>) -> &'a Node;

    fn ty(self, m: &mut Module) -> Self;
}
impl ValExt for Val {
    fn get<'a>(self, slots: &'a ReadStorage<Slot>) -> &'a Node {
        slots.node(self).unwrap()
    }

    fn ty(self, m: &mut Module) -> Self {
        let slots = m.slots();
        let n = self.get(&slots).clone();
        drop(slots);
        n.ty(m)
    }
}

/*
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
*/

#[derive(Debug, Clone, Eq, PartialEq, Component)]
pub enum Slot {
    Full(Node),
    Redirect(Val),
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

pub trait Slots {
    fn node(&self, i: Val) -> Option<&Node>;
    fn unredirect(&self, v: Val) -> Val;
    fn fun(&self, i: Val) -> Option<&Function>;
}
impl Slots for ReadStorage<'_, Slot> {
    fn fun(&self, i: Val) -> Option<&Function> {
        match self.node(i)? {
            Node::Fun(f) => Some(f),
            _ => None,
        }
    }
    fn node(&self, i: Val) -> Option<&Node> {
        let mut i = i;
        loop {
            match self.get(i)? {
                Slot::Full(x) => break Some(x),
                Slot::Redirect(v) => i = *v,
            }
        }
    }
    fn unredirect(&self, v: Val) -> Val {
        match self.get(v) {
            Some(Slot::Redirect(x)) => self.unredirect(*x),
            _ => v,
        }
    }
}

macro_rules! wrapper {
    {} => {};
    {
        #[derive $traits:tt]
        pub struct $n:ident($inner:ty); $($rest:tt)*
    } => {
        #[derive $traits]
        pub struct $n($inner);
        impl std::ops::Deref for $n {
            type Target = $inner;
            fn deref(&self) -> &$inner {
                &self.0
            }
        }
        impl std::ops::DerefMut for $n {
            fn deref_mut(&mut self) -> &mut $inner {
                &mut self.0
            }
        }

        wrapper!{$($rest)*}
    };
}

wrapper! {
    #[derive(Clone, Debug, Component)]
    pub struct Uses(Vec<Val>);

    #[derive(Clone, Debug, Component)]
    pub struct Name(String);
}

// #[derive(Debug, Clone, Eq, PartialEq)]
pub struct Module {
    pub world: World,
}
impl Module {
    pub fn new() -> Self {
        let mut world = World::new();
        world.register::<Slot>();
        world.register::<Uses>();
        world.register::<Name>();
        Module { world }
    }

    /// Removes a node from the module. Panics if that node is used by anything.
    pub fn remove(&mut self, i: Val) {
        if !self.uses().get(i).map_or(true, |x| x.0.is_empty()) {
            panic!("Error: cannot delete node with uses!")
        }
        self.world.delete_entity(i).unwrap();
    }

    pub fn slots(&self) -> ReadStorage<Slot> {
        self.world.read_storage()
    }

    pub fn slots_mut(&self) -> WriteStorage<Slot> {
        self.world.write_storage()
    }

    pub fn uses(&self) -> ReadStorage<Uses> {
        self.world.read_storage()
    }

    pub fn name(&self, i: Val) -> Option<String> {
        self.world
            .read_storage::<Name>()
            .get(i)
            .map(|x| x.0.clone())
    }

    pub fn set_name(&mut self, i: Val, n: String) {
        self.world
            .write_storage::<Name>()
            .insert(i, Name(n))
            .unwrap();
    }

    // TODO deduplicate constants, or just everything except functions (implicit CSE)
    pub fn add(&mut self, x: Node, n: Option<String>) -> Val {
        let args = x.args();

        // Add to the ECS
        let e = self
            .world
            .create_entity()
            .with(Slot::Full(x))
            .with(Uses(Vec::new()));
        let e = if let Some(n) = n { e.with(Name(n)) } else { e };
        let e = e.build();

        // Add uses for the things the new value uses
        for i in args {
            let i = self.slots().unredirect(i);
            self.world
                .write_storage::<Uses>()
                .get_mut(i)
                .unwrap()
                .0
                .push(e);
        }
        e
    }

    /// Reserves space for a value. Used for forward references.
    /// Fill the value later with `replace()`.
    pub fn reserve(&mut self, n: Option<String>) -> Val {
        // Add to the ECS, without a Slot component
        let e = self.world.create_entity().with(Uses(Vec::new()));
        let e = if let Some(n) = n { e.with(Name(n)) } else { e };
        e.build()
    }

    pub fn redirect(&mut self, from: Val, to: Val) {
        self.world
            .write_storage()
            .insert(from, Slot::Redirect(to))
            .unwrap();
        // If we use redirect() to give this node a name, transfer that over
        if self.name(to).is_none() {
            if let Some(name) = self.name(from) {
                self.world
                    .write_storage()
                    .insert(to, Name(name.clone()))
                    .unwrap();
            }
        }

        // Transfer any uses from the alias to the pointee
        // Removes any uses of 'from' and adds them to 'to'
        let mut uses = self.world.write_storage::<Uses>();
        let from = uses.get_mut(from).unwrap();
        let mut new = Vec::new();
        std::mem::swap(&mut from.0, &mut new);
        let to = uses.get_mut(to).unwrap();
        to.0.append(&mut new);
    }

    pub fn replace(&mut self, v: Val, x: Node) {
        // Since there aren't usually many arguments, it's simplest to just remove old uses and add new ones
        let old_args = self
            .world
            .read_storage::<Slot>()
            .get(v)
            .map(Slot::to_option)
            .flatten()
            .map_or(SmallVec::new(), |x| x.args());
        let new_args = x.args();

        let mut uses = self.world.write_storage::<Uses>();
        for i in old_args {
            let i = self.slots().unredirect(i);
            let u = &mut uses.get_mut(i).unwrap().0;
            let i = u.iter().position(|&x| x == v).unwrap();
            u.swap_remove(i);
        }
        for i in new_args {
            let i = self.slots().unredirect(i);
            uses.get_mut(i).unwrap().0.push(v);
        }

        self.world.write_storage().insert(v, Slot::Full(x)).unwrap();
    }

    pub fn unredirect(&self, v: Val) -> Val {
        match self.world.read_storage::<Slot>().get(v) {
            Some(Slot::Redirect(x)) => self.unredirect(*x),
            _ => v,
        }
    }

    pub fn top_level(&self) -> Vec<Val> {
        (&self.world.entities(), &self.world.read_storage::<Slot>())
            .join()
            .filter(move |(x, slot)| {
                // A node is top-level if it:
                // 1. is a function (and not a redirect)
                if !matches!(slot, Slot::Full(Node::Fun(_))) {
                    return false;
                }

                // 2. doesn't use parameters from other functions at runtime
                fn has_param(m: &Module, x: Val, not: &mut HashSet<Val>) -> bool {
                    let x = m.unredirect(x);
                    match m.slots().node(x) {
                        None => unreachable!(),
                        Some(Node::Param(p, _)) => {
                            !not.contains(p) && matches!(m.slots().node(*p), Some(Node::Fun(_)))
                        }
                        Some(Node::Fun(_)) | Some(Node::FunType(_)) | Some(Node::ProdType(_)) => {
                            if !not.contains(&x) {
                                // If it calls another function, that function can use its own parameters
                                not.insert(x);
                                let b = m
                                    .slots()
                                    .node(x)
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
            .map(|(x, _)| x)
            .collect()
    }

    pub fn vals(&self) -> Vec<Val> {
        self.world
            .entities()
            .join()
            .filter(move |x| self.slots().node(*x).is_some())
            .collect()
    }

    /// Returns a list of all foreign parameters this node depends on, with their types.
    pub fn env(&self, v: Val) -> Vec<(Val, Val)> {
        fn go(m: &Module, v: Val, seen: &mut HashSet<Val>, acc: &mut HashSet<(Val, Val)>) {
            let v = m.unredirect(v);
            match m.slots().node(v).unwrap() {
                Node::Param(f, i) => {
                    if seen.contains(f) {
                    } else {
                        match m.slots().node(*f).unwrap() {
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
            let v = m.unredirect(v);
            match m.slots().node(v).unwrap() {
                Node::Param(f, _) => {
                    if seen.contains(f) {
                    } else {
                        match m.slots().node(*f).unwrap() {
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
        for i in self.world.entities().join() {
            // Skip redirects for this
            if i != self.unredirect(i) {
                continue;
            }
            // Also skip anything but functions
            if !matches!(self.slots().node(i), Some(Node::Fun(_))) {
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

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum RefOp {
    /// RefNew(inner_ty)
    RefNew(Val),
    /// RefGet(ref)
    RefGet(Val),
    /// RefSet(ref, new_val)
    RefSet(Val, Val),
}
impl RefOp {
    pub fn runtime_args(self) -> SmallVec<[Val; 4]> {
        match self {
            RefOp::RefGet(v) | RefOp::RefNew(v) => smallvec![v],
            RefOp::RefSet(v, n) => smallvec![v, n],
        }
    }
    pub fn args(self) -> SmallVec<[Val; 4]> {
        match self {
            RefOp::RefGet(v) | RefOp::RefNew(v) => smallvec![v],
            RefOp::RefSet(v, n) => smallvec![v, n],
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Node {
    Fun(Function),
    FunType(usize),
    ExternFun(String, SmallVec<[Val; 3]>, Val),
    /// Extern functions have a return type
    ExternFunType(SmallVec<[Val; 3]>, Val),
    ProdType(SmallVec<[Val; 4]>),
    SumType(SmallVec<[Val; 4]>),
    /// IfCase(tag, x); then and else are passed to it as arguments
    IfCase(usize, Val),
    ExternCall(Val),
    If(Val),
    Ref(RefOp),
    RefTy(Val),
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
            Node::ProdType(v) => v.clone(),
            Node::BinOp(_, a, b) => smallvec![*a, *b],
            Node::IfCase(_, x)
            | Node::Proj(x, _)
            | Node::Inj(_, _, x)
            | Node::If(x)
            | Node::RefTy(x)
            | Node::ExternCall(x) => {
                smallvec![*x]
            }
            Node::FunType(_) | Node::SumType(_) => SmallVec::new(),
            Node::ExternFun(_, _, _) | Node::ExternFunType(_, _) => SmallVec::new(),
            Node::Const(_) => SmallVec::new(),
            // `f` not being known at runtime doesn't really make sense
            Node::Param(_f, _) => SmallVec::new(),
            Node::Ref(r) => r.runtime_args(),
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
            Node::ProdType(v) | Node::SumType(v) => v.clone(),
            Node::ExternFun(_, v, r) | Node::ExternFunType(v, r) => {
                v.iter().copied().chain(std::iter::once(*r)).collect()
            }
            Node::Param(f, _) => smallvec![*f],
            Node::BinOp(_, a, b) | Node::Inj(a, _, b) => smallvec![*a, *b],
            Node::FunType(_) | Node::Const(_) => SmallVec::new(),
            Node::IfCase(_, x)
            | Node::Proj(x, _)
            | Node::If(x)
            | Node::ExternCall(x)
            | Node::RefTy(x) => {
                smallvec![*x]
            }
            Node::Ref(r) => r.args(),
        }
    }

    pub fn ty(&self, m: &mut Module) -> Val {
        match self {
            Node::Fun(f) => m.add(Node::FunType(f.params.len()), None),
            Node::ExternFun(_, p, r) => m.add(Node::ExternFunType(p.clone(), *r), None),
            Node::ExternCall(t) => {
                let ty = t.ty(m);
                let slots = m.slots();
                match ty.get(&slots) {
                    Node::ExternFunType(p, _) => {
                        let l = p.len();
                        drop(slots);
                        m.add(Node::FunType(l + 1), None)
                    }
                    _ => unreachable!(),
                }
            }
            Node::FunType(_)
            | Node::ProdType(_)
            | Node::SumType(_)
            | Node::ExternFunType(_, _)
            | Node::RefTy(_) => m.add(Node::Const(Constant::TypeType), None),
            Node::Product(ty, _) => *ty,
            Node::Param(f, i) => match m.slots().node(*f).unwrap() {
                Node::Fun(f) => f.params[*i as usize],
                Node::ProdType(p) => p[*i as usize],
                _ => unreachable!(),
            },
            Node::Const(c) => match c {
                Constant::TypeType | Constant::IntType(_) => {
                    m.add(Node::Const(Constant::TypeType), None)
                }
                Constant::Int(w, _) => m.add(Node::Const(Constant::IntType(*w)), None),
                Constant::Stop | Constant::Unreachable => m.add(Node::FunType(0), None),
            },
            Node::BinOp(BinOp::IEq, _, _) => m.add(Node::Const(Constant::IntType(Width::W1)), None),
            Node::BinOp(_, a, _) => a.ty(m),
            Node::If(_) => {
                // Takes `then` and `else` blocks as arguments
                m.add(Node::FunType(2), None)
            }
            Node::Ref(_) => {
                // Takes just a continuation
                m.add(Node::FunType(1), None)
            }
            Node::IfCase(_, _) => {
                // Takes `then` and `else` blocks as arguments
                m.add(Node::FunType(2), None)
            }
            Node::Proj(x, i) => match x.ty(m).get(&m.slots()) {
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
