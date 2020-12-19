use crate::ir::*;
use smallvec::*;

pub struct Pi {
    pub arg: Val,
    from: Val,
}

pub struct Sigma {
    val: Val,
    tys: SmallVec<[Val; 4]>,
}
impl Sigma {
    /// Returns the argument
    pub fn add(&mut self, ty: Val, b: &mut Builder) -> Val {
        let i = self.tys.len() as u8;
        self.tys.push(ty);
        b.module.add(Node::Param(self.val, i), None)
    }

    pub fn finish(self, b: &mut Builder) -> Val {
        b.module.replace(self.val, Node::ProdType(self.tys));
        self.val
    }
}

/// Takes care of the transformation from direct style to CPS.
pub struct Builder<'m> {
    module: &'m mut Module,
    block: Val,
    params: Vec<Val>,
    /// (fun, block, params, cont)
    funs: Vec<(Val, Val, Vec<Val>, Val)>,
}
impl<'m> Builder<'m> {
    pub fn new(m: &'m mut Module) -> Self {
        let block = m.reserve(None);
        Builder {
            module: m,
            block,
            params: Vec::new(),
            funs: Vec::new(),
        }
    }

    // TODO: should this just be a Drop impl?
    pub fn finish(&mut self) {
        let stop = self.module.add(Node::Const(Constant::Stop), None);
        self.module.replace(
            self.block,
            Node::Fun(Function {
                params: self.params.drain(0..).collect(),
                callee: stop,
                call_args: smallvec![],
            }),
        )
    }

    pub fn call(&mut self, f: Val, x: Val, ret_ty: Val) -> Val {
        let cont = self.module.reserve(None);
        self.module.replace(
            self.block,
            Node::Fun(Function {
                params: self.params.drain(0..).collect(),
                callee: f,
                call_args: smallvec![x, cont],
            }),
        );
        self.block = cont;
        self.params.push(ret_ty);
        self.module.add(Node::Param(cont, 0), None)
    }

    pub fn cons(&mut self, c: Constant) -> Val {
        self.module.add(Node::Const(c), None)
    }

    /// Starts an empty sigma type
    pub fn sigma(&mut self) -> Sigma {
        Sigma {
            val: self.module.reserve(None),
            tys: SmallVec::new(),
        }
    }

    /// Shortcut function to create a non-dependent product type
    pub fn prod_type(&mut self, v: impl Into<SmallVec<[Val; 4]>>) -> Val {
        self.module.add(Node::ProdType(v.into()), None)
    }

    pub fn sum_type(&mut self, v: impl Into<SmallVec<[Val; 4]>>) -> Val {
        self.module.add(Node::SumType(v.into()), None)
    }

    pub fn product(&mut self, ty: Val, v: impl Into<SmallVec<[Val; 3]>>) -> Val {
        self.module.add(Node::Product(ty, v.into()), None)
    }

    pub fn inject_sum(&mut self, ty: Val, idx: usize, val: Val) -> Val {
        self.module.add(Node::Inj(ty, idx, val), None)
    }

    pub fn fun_type(&mut self, from: Val, to: Val) -> Val {
        let cont_ty = self.module.add(Node::FunType(smallvec![to]), None);
        self.module
            .add(Node::FunType(smallvec![from, cont_ty]), None)
    }

    pub fn start_pi(&mut self, param: Option<String>, from: Val) -> Pi {
        Pi {
            arg: self.module.reserve(param),
            from,
        }
    }

    pub fn end_pi(&mut self, pi: Pi, to: Val) -> Val {
        let Pi { arg, from } = pi;
        let cont_ty = self.module.add(Node::FunType(smallvec![to]), None);
        let fun = self
            .module
            .add(Node::FunType(smallvec![from, cont_ty]), None);
        self.module.replace(arg, Node::Param(fun, 0));
        fun
    }

    pub fn reserve(&mut self, name: Option<String>) -> Val {
        self.module.reserve(name)
    }

    /// Returns the parameter value
    pub fn push_fun(&mut self, param: Option<String>, param_ty: Val) -> Val {
        let fun = self.module.reserve(None);
        let cont = self.module.add(Node::Param(fun, 1), None);
        self.funs.push((fun, self.block, self.params.clone(), cont));
        self.block = fun;
        // Skip adding the continuation parameter and add it later, since we might not know the return type yet
        self.params = vec![param_ty];
        self.module.add(Node::Param(fun, 0), param)
    }

    pub fn pop_fun(&mut self, ret: Val, ret_ty: Val) -> Val {
        let (fun, block, params, cont) = self.funs.pop().unwrap();

        // Add the continuation parameter to the function
        let cont_ty = self.module.add(Node::FunType(smallvec![ret_ty]), None);
        match self.module.get_mut(fun) {
            Some(Node::Fun(f)) => {
                f.params.push(cont_ty);
            }
            // The function returns a value directly, so we'll just add the continuation parameter to the function node we're making now
            None => {
                self.params.push(cont_ty);
            }
            _ => unreachable!(),
        }

        // We don't use self.call since we don't add the cont parameter here
        self.module.replace(
            self.block,
            Node::Fun(Function {
                params: self.params.drain(0..).collect(),
                callee: cont,
                call_args: smallvec![ret],
            }),
        );
        self.block = block;
        self.params = params;
        fun
    }
}
