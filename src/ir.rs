use smallvec::*;
pub use specs::prelude::{Join, World, WorldExt};
use specs::{prelude::*, Component};
use std::collections::{HashMap, HashSet};

pub type Val = Entity;

pub trait ValExt {
    fn get<'a>(self, slots: &'a ReadStorage<Slot>) -> &'a Node;

    fn ty(self, m: &mut Module) -> Self;

    fn name_or_num(self, n: &ReadStorage<Name>) -> String;
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

    fn name_or_num(self, n: &ReadStorage<Name>) -> String {
        n.get(self)
            .map(|n| n.0.clone())
            .unwrap_or_else(|| format!("{}", self.id()))
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

    /// Returns a list of all foreign parameters this node depends on, with their types.
    fn env(&self, v: Val) -> Vec<(Val, Val)> {
        fn go(
            m: &(impl Slots + ?Sized),
            v: Val,
            seen: &mut HashSet<Val>,
            acc: &mut Vec<(Val, Val)>,
        ) {
            let v = m.unredirect(v);
            match m.node(v).unwrap() {
                Node::Param(f, i) => {
                    if seen.contains(f) {
                    } else {
                        match m.node(*f).unwrap() {
                            Node::Fun(Function { params, .. }) => {
                                if !acc.contains(&(v, params[*i as usize])) {
                                    acc.push((v, params[*i as usize]));
                                }
                                // go(m, params[*i as usize], seen, acc);
                            }
                            // Parameters of sigma types don't count
                            Node::ProdType(_) => (),
                            _ => unreachable!(),
                        }
                    }
                }
                n => {
                    if !seen.contains(&v) {
                        seen.insert(v);
                        for i in n.runtime_args() {
                            go(m, i, seen, acc)
                        }
                        seen.remove(&v);
                    }
                }
            }
        }
        let mut acc = Vec::new();
        go(self, v, &mut HashSet::new(), &mut acc);
        acc //.into_iter().collect()
    }
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
        pub struct $n(pub $inner);
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

    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Component)]
    pub struct ValType(Val);
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
        world.register::<ValType>();
        Module { world }
    }

    pub fn add_types(&mut self) {
        let entities: Vec<_> = self
            .world
            .entities()
            .join()
            .filter(|e| self.slots().get(*e).and_then(|x| x.to_option()).is_some())
            .collect::<Vec<_>>();
        let tys: Vec<_> = entities.into_iter().map(|e| (e, e.ty(self))).collect();
        let mut types = self.world.write_storage::<ValType>();
        for (e, t) in tys {
            types.insert(e, ValType(t)).unwrap();
        }
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
    RefNew,
    /// RefGet(ref)
    RefGet(Val),
    /// RefSet(ref, new_val)
    RefSet(Val, Val),
}
impl RefOp {
    pub fn runtime_args(self) -> SmallVec<[Val; 4]> {
        match self {
            RefOp::RefNew => smallvec![],
            RefOp::RefGet(v) => smallvec![v],
            RefOp::RefSet(v, n) => smallvec![v, n],
        }
    }
    pub fn args(self) -> SmallVec<[Val; 4]> {
        self.runtime_args()
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
    Unbox(Val),
    /// IfCase(tag, x); then and else are passed to it as arguments
    IfCase(usize, Val),
    /// ExternCall(fun, ret_ty)
    ExternCall(Val, Val),
    If(Val),
    /// Ref(inner_ty, op)
    Ref(Val, RefOp),
    RefTy(Val),
    /// Proj(ty, val, i): Projecting a numbered member of a product type
    Proj(Val, Val, usize),
    /// Inj(ty, i, payload): Injecting a numbered member of a sum type
    Inj(Val, usize, Val),
    Product(Val, SmallVec<[Val; 3]>),
    /// The `Val` should point to a function
    Param(Val, u8),
    Const(Constant),
    BinOp(BinOp, Signed, Val, Val),
}
impl Node {
    /// Arguments that, *if they're only known at runtime*, exist in the generated LLVM IR.
    /// So, not types of things.
    pub fn runtime_args(&self) -> SmallVec<[Val; 4]> {
        // return self.args();
        match self {
            Node::Fun(Function {
                callee,
                call_args,
                params,
            }) => call_args
                .iter()
                .chain(params)
                .copied()
                .chain(std::iter::once(*callee))
                .collect(),
            Node::Product(t, v) => v.iter().copied().chain(std::iter::once(*t)).collect(),
            Node::ProdType(v) | Node::SumType(v) => v.clone(),
            Node::BinOp(_, _, a, b) | Node::Proj(a, b, _) => smallvec![*a, *b],
            Node::IfCase(_, x)
            | Node::Inj(_, _, x)
            | Node::If(x)
            | Node::RefTy(x)
            | Node::Unbox(x)
            | Node::ExternCall(x, _) => {
                smallvec![*x]
            }
            Node::FunType(_) => SmallVec::new(),
            Node::ExternFun(_, _, _) | Node::ExternFunType(_, _) => SmallVec::new(),
            Node::Const(_) => SmallVec::new(),
            // `f` not being known at runtime doesn't really make sense
            Node::Param(_f, _) => SmallVec::new(),
            Node::Ref(ty, r) => {
                let mut v = r.runtime_args();
                v.push(*ty);
                v
            }
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
            Node::BinOp(_, _, a, b)
            | Node::Inj(a, _, b)
            | Node::Proj(a, b, _)
            | Node::ExternCall(a, b) => smallvec![*a, *b],
            Node::FunType(_) | Node::Const(_) => SmallVec::new(),
            Node::IfCase(_, x) | Node::If(x) | Node::Unbox(x) | Node::RefTy(x) => {
                smallvec![*x]
            }
            Node::Ref(ty, r) => {
                let mut v = r.args();
                v.push(*ty);
                v
            }
        }
    }

    pub fn ty(&self, m: &mut Module) -> Val {
        match self {
            Node::Fun(f) => m.add(Node::FunType(f.params.len()), None),
            Node::ExternFun(_, p, r) => m.add(Node::ExternFunType(p.clone(), *r), None),
            Node::ExternCall(t, _) => {
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
            | Node::Unbox(_)
            | Node::RefTy(_) => m.add(Node::Const(Constant::TypeType), None),
            Node::Product(ty, _) => *ty,
            Node::Param(f, i) => match m.slots().node(*f).unwrap() {
                Node::Fun(f) => f.params[*i as usize],
                Node::ProdType(p) => p[*i as usize],
                Node::ExternFun(_, p, _) => p[*i as usize],
                _ => unreachable!(),
            },
            Node::Const(c) => match c {
                Constant::TypeType
                | Constant::IntType(_)
                | Constant::FloatType(_)
                | Constant::BoxTy
                | Constant::StringTy => m.add(Node::Const(Constant::TypeType), None),
                Constant::Int(w, _) => m.add(Node::Const(Constant::IntType(*w)), None),
                Constant::Stop | Constant::Unreachable => m.add(Node::FunType(0), None),
                Constant::Float(Float::F32(_)) => {
                    m.add(Node::Const(Constant::FloatType(FloatType::F32)), None)
                }
                Constant::Float(Float::F64(_)) => {
                    m.add(Node::Const(Constant::FloatType(FloatType::F64)), None)
                }
                Constant::String(_) => m.add(Node::Const(Constant::StringTy), None),
            },
            Node::BinOp(op, _, _, _) if op.is_comp() => {
                m.add(Node::Const(Constant::IntType(Width::W1)), None)
            }
            Node::BinOp(_, _, a, _) => a.ty(m),
            Node::If(_) => {
                // Takes `then` and `else` blocks as arguments
                m.add(Node::FunType(2), None)
            }
            Node::Ref(_, _) => {
                // Takes just a continuation
                m.add(Node::FunType(1), None)
            }
            Node::IfCase(_, _) => {
                // Takes `then` and `else` blocks as arguments
                m.add(Node::FunType(2), None)
            }
            Node::Proj(t, _, i) => match m.slots().node(*t).unwrap() {
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

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum FloatType {
    F32,
    F64,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Float {
    F32(u32),
    F64(u64),
}

/// Types are generally constants
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Constant {
    Stop,
    Unreachable,
    TypeType,
    BoxTy,
    IntType(Width),
    Int(Width, i64),
    FloatType(FloatType),
    Float(Float),
    StringTy,
    String(String),
}

pub type Signed = bool;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
    Mod,
    And,
    Or,
    Xor,
    Shl,
    Shr,
    Eq,
    NEq,
    Gt,
    Lt,
    Geq,
    Leq,
}
impl BinOp {
    pub fn is_comp(self) -> bool {
        use BinOp::*;
        matches!(self, Eq | NEq | Gt | Lt | Geq | Leq)
    }
}

mod display {
    use super::*;

    impl std::fmt::Display for Constant {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            match self {
                Constant::Unreachable => write!(f, "unreachable"),
                Constant::Stop => write!(f, "stop"),
                Constant::TypeType => write!(f, "Type"),
                Constant::BoxTy => write!(f, "box"),
                Constant::IntType(w) => write!(f, "I{}", w),
                Constant::Int(w, i) => write!(f, "{}i{}", i, w),
                Constant::FloatType(t) => write!(f, "{}", t),
                Constant::Float(x) => write!(f, "{}", x),
                Constant::StringTy => write!(f, "String"),
                Constant::String(s) => write!(f, "{:?}", s),
            }
        }
    }
    impl std::fmt::Display for FloatType {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            match self {
                FloatType::F32 => write!(f, "F32"),
                FloatType::F64 => write!(f, "F64"),
            }
        }
    }
    impl std::fmt::Display for Float {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            match self {
                Float::F32(x) => write!(f, "{}", f32::from_bits(*x)),
                Float::F64(x) => write!(f, "{}", f64::from_bits(*x)),
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
                BinOp::Eq => write!(f, "=="),
                BinOp::Add => write!(f, "+"),
                BinOp::Sub => write!(f, "-"),
                BinOp::Mul => write!(f, "*"),
                BinOp::Div => write!(f, "/"),
                BinOp::Pow => write!(f, "**"),
                BinOp::Mod => write!(f, "%"),
                BinOp::And => write!(f, "&"),
                BinOp::Or => write!(f, "|"),
                BinOp::Xor => write!(f, "^"),
                BinOp::Shl => write!(f, "<<"),
                BinOp::Shr => write!(f, ">>"),
                BinOp::NEq => write!(f, "!="),
                BinOp::Gt => write!(f, ">"),
                BinOp::Lt => write!(f, "<"),
                BinOp::Geq => write!(f, ">="),
                BinOp::Leq => write!(f, "<="),
            }
        }
    }
}
