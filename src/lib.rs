use smallvec::*;
use either::Either;
use std::collections::HashMap;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Val(usize);
pub type Ty = Val;

#[derive(Default, Debug)]
pub struct Module {
    nodes: Vec<Option<Node>>,
    uses: Vec<Vec<Val>>,
}
impl Module {
    pub fn get(&self, i: Val) -> Option<&Node> {
        self.nodes.get(i.0).map(|x| x.as_ref()).flatten()
    }

    pub fn uses(&self, i: Val) -> &Vec<Val> {
        self.uses.get(i.0).unwrap()
    }

    // TODO deduplicate constants, or just everything (implicit CSE)
    pub fn add(&mut self, x: Node) -> Val {
        let args = x.args();
        let v = Val(self.nodes.len());
        self.nodes.push(Some(x));
        self.uses.push(Vec::new());

        // Add uses for the things the new value uses
        for i in args {
            self.uses[i.0].push(v);
        }

        v
    }

    /// Reserves space for a value. Used for forward references.
    /// Fill the value later with `replace()`.
    pub fn reserve(&mut self) -> Val {
        let v = Val(self.nodes.len());
        self.nodes.push(None);
        self.uses.push(Vec::new());
        v
    }

    pub fn replace(&mut self, v: Val, x: Node) {
        // Since there aren't usually many arguments, it's simplest to just remove old uses and add new ones
        let old_args = self.nodes[v.0].as_ref().map_or(SmallVec::new(), |x| x.args());
        let new_args = x.args();

        for i in old_args {
            let u = &mut self.uses[i.0];
            let i = u.iter().position(|&x| x == v).unwrap();
            u.swap_remove(i);
        }
        for i in new_args {
            self.uses[i.0].push(v);
        }

        self.nodes[v.0] = Some(x);
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Node {
    Fun(Function),
    /// The `Val` should point to a function
    Param(Val, u8),
    Const(Constant),
    BinOp(BinOp, Val, Val),
}
impl Node {
    pub fn args(&self) -> SmallVec<[Val; 4]> {
        match self {
            Node::Fun(Function {
                params,
                callee,
                call_args,
            }) => params.iter().chain(call_args.iter()).copied().chain(std::iter::once(*callee)).collect(),
            Node::Param(f, _) => smallvec![*f],
            Node::BinOp(_, a, b) => smallvec![*a, *b],
            Node::Const(_) => SmallVec::new(),
        }
    }

    pub fn ty(&self, m: &Module) -> Either<Constant, Ty> {
        match self {
            Node::Fun(_) => Either::Left(Constant::FunType),
            Node::Param(f, i) => {
                if let Node::Fun(f) = m.get(*f).unwrap() {
                    Either::Right(f.params[*i as usize])
                } else {
                    panic!("non-function has no params")
                }
            }
            Node::Const(c) => match c {
                Constant::TypeType
                | Constant::IntType(_)
                | Constant::FunType => Either::Left(Constant::TypeType),
                Constant::Int(w, _) => Either::Left(Constant::IntType(*w)),
            },
            // Comparison operations will need a special case here
            Node::BinOp(_, a, _) => m.get(*a).unwrap().ty(m),
        }
    }

    pub fn mangle(self, m: &mut Module, map: &HashMap<Val, Val>) -> Self {
        match self {
            Node::Fun(mut f) => {
                f.params.iter_mut().for_each(|x| *x = x.mangle(m, map));
                f.callee = f.callee.mangle(m, map);
                f.call_args.iter_mut().for_each(|x| *x = x.mangle(m, map));
                Node::Fun(f)
            }
            Node::Param(f, i) => {
                Node::Param(
                    f.mangle(m, map),
                    i,
                )
            }
            Node::BinOp(op, a, b) => Node::BinOp(
                op,
                a.mangle(m, map),
                b.mangle(m, map),
            ),
            // Constants can't use other values
            Node::Const(c) => Node::Const(c),
        }
    }
}
impl Val {
    pub fn mangle(self, m: &mut Module, map: &HashMap<Val, Val>) -> Self {
        if let Some(&x) = map.get(&self) {
            x
        } else {
            if let Some(new) = m.get(self).cloned().map(|x| x.mangle(m, map)) {
                m.add(new)
            } else {
                // Assume it doesn't use things in `map`, I guess?
                self
            }
        }
    }
}

/// A function body is just a call
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Function {
    pub params: SmallVec<[Ty; 3]>,
    pub callee: Val,
    pub call_args: SmallVec<[Val; 3]>,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Width {
    W8,
    W16,
    W32,
    W64,
}

/// Types are generally constants
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum Constant {
    TypeType,
    IntType(Width),
    FunType,
    Int(Width, u64),
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum BinOp {
    IAdd,
    ISub,
    IMul,
    IDiv,
}


pub fn lift(m: &mut Module, vfun: Val, to_lift: Val) -> Val {
    // Clone the function
    let fun = m.get(vfun).expect("lift() on nonexistent function").clone();
    let mut fun = if let Node::Fun(fun) = fun { fun } else { panic!("lift() on non-function") };


    // Add the new parameter
    let ty = m.get(to_lift).unwrap().ty(m).right_or_else(|x| m.add(Node::Const(x)));
    let nparams = fun.params.len();
    fun.params.push(ty);

    // Update references to the old function's parameters in the body of `fun` to the new parameters
    let fnew = m.reserve();
    let lifted = m.add(Node::Param(fnew, nparams as u8));
    let mut map = HashMap::new();
    // We're modifying `m` in the loop, so we need to `clone()` here
    for i in m.uses(vfun).clone() {
        let new = match m.get(i).unwrap() {
            // A known call of the function should be switch to calling the new one
            Node::Fun(f) if f.callee == vfun => {
                // To call the new function, though, it needs to pass it the new parameter
                let mut call_args = f.call_args.clone();
                call_args.push(lifted);
                Some(Node::Fun(
                    Function {
                        params: f.params.clone(),
                        callee: fnew,
                        call_args,
                    }
                ))
            }
            // If it's referencing a parameter, we just switch the function
            Node::Param(f, i) => {
                assert_eq!(*f, vfun);
                Some(Node::Param(fnew, *i))
            }
            _ => None,
        };
        if let Some(new) = new {
            let new = m.add(new);
            map.insert(i, new);
        }
    }

    // Update references to `to_lift` to the new parameter
    map.insert(to_lift, lifted);

    // Actually apply both replacements
    let fun = Node::Fun(fun).mangle(m, &map);
    m.replace(fnew, fun);
    fnew
}

mod display {
    use super::*;

    /// Displays [a, b, c as "a, b, c" using the Display impl of `T`
    pub struct DisplayVec<T>(T);
    impl<T> std::fmt::Display for DisplayVec<T>
        where T: IntoIterator + Clone, T::Item: std::fmt::Display {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            let mut first = true;
            for i in self.0.clone() {
                if !first {
                    write!(f, ", ")?;
                }
                first = false;
                write!(f, "{}", i)?;
            }
            Ok(())
        }
    }

    impl std::fmt::Display for Node {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            match self {
                Node::Fun(Function {
                    params,
                    callee,
                    call_args,
                }) => {
                    write!(f, "fun({}) => {}({})", DisplayVec(params), callee, DisplayVec(call_args))
                }
                Node::Param(fun, i) => {
                    write!(f, "param {}[{}]", fun, i)
                }
                Node::Const(c) => match c {
                    Constant::TypeType => write!(f, "Type"),
                    Constant::IntType(w) => write!(f, "I{}", w),
                    Constant::FunType => write!(f, "fun"),
                    Constant::Int(_, i) => write!(f, "{}", i),
                }
                Node::BinOp(op, a, b) => write!(f, "{:?} {} {:?}", a, op, b),
            }
        }
    }
    impl std::fmt::Display for Width {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            match self {
                Width::W8 => write!(f, "8"),
                Width::W16 => write!(f, "16"),
                Width::W32 => write!(f, "32"),
                Width::W64 => write!(f, "64"),
            }
        }
    }
    impl std::fmt::Display for BinOp {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            match self {
                BinOp::IAdd => write!(f, "+"),
                BinOp::ISub => write!(f, "-"),
                BinOp::IMul => write!(f, "*"),
                BinOp::IDiv => write!(f, "/"),
            }
        }
    }
    impl std::fmt::Display for Val {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "%{}", self.0)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lifting() {
        let mut m = Module::default();
        let (before, to_lift) = {
            let u32_t = m.add(Node::Const(Constant::IntType(Width::W32)));
            let enclosing = m.reserve();
            // TODO working forward references
            let param_0 = m.add(Node::Param(enclosing, 0));

            let before = m.add(Node::Fun(Function {
                params: SmallVec::new(),
                callee: enclosing,
                call_args: smallvec![param_0],
            }));
            m.replace(enclosing, Node::Fun(Function {
                params: smallvec![u32_t],
                callee: before,
                call_args: SmallVec::new(),
            }));
            (before, param_0)
        };

        // So we can see in the output where the lifting happened
        m.add(Node::Const(Constant::Int(Width::W64, 111111111111)));

        let after = lift(&mut m, before, to_lift);
        for (i, n) in m.nodes.iter().enumerate() {
            println!("%{} = {}", i, n.as_ref().unwrap());
        }
        panic!("look right?");
    }
}
