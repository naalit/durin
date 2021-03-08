use crate::ir::*;
use smallvec::*;

pub struct Pi {
    pub args: SmallVec<[Val; 4]>,
    tys: SmallVec<[Val; 4]>,
}
impl Pi {
    pub fn add_arg(&mut self, ty: Val, builder: &mut Builder) {
        self.tys.push(ty);
        let arg = builder.reserve(None);
        self.args.push(arg);
    }
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
    /// (continuation, else block)
    ifs: Vec<(Val, Option<Val>)>,
}
impl<'m> Builder<'m> {
    pub fn new(m: &'m mut Module) -> Self {
        let block = m.reserve(None);
        Builder {
            module: m,
            block,
            params: Vec::new(),
            funs: Vec::new(),
            ifs: Vec::new(),
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

    pub fn cont(&self) -> Option<Val> {
        self.funs.last().map(|x| x.3)
    }

    /// Updates `from` to be an alias of `to`
    pub fn redirect(&mut self, from: Val, to: Val) {
        self.module.redirect(from, to);
    }

    pub fn call(&mut self, f: Val, args: impl Into<SmallVec<[Val; 3]>>, ret_ty: Val) -> Val {
        let cont = self.module.reserve(None);
        let mut args = args.into();
        args.push(cont);
        self.module.replace(
            self.block,
            Node::Fun(Function {
                params: self.params.drain(0..).collect(),
                callee: f,
                call_args: args,
            }),
        );
        self.block = cont;
        self.params.push(ret_ty);
        self.module.add(Node::Param(cont, 0), None)
    }

    pub fn call_multi(
        &mut self,
        f: Val,
        args: impl Into<SmallVec<[Val; 3]>>,
        ret_tys: &[Val],
    ) -> Vec<Val> {
        let cont = self.module.reserve(None);
        let mut args = args.into();
        args.push(cont);
        self.module.replace(
            self.block,
            Node::Fun(Function {
                params: self.params.drain(0..).collect(),
                callee: f,
                call_args: args,
            }),
        );
        self.block = cont;
        self.params.extend(ret_tys);
        ret_tys
            .iter()
            .enumerate()
            .map(|(i, _)| self.module.add(Node::Param(cont, i as u8), None))
            .collect()
    }

    /// Calls a function without adding and passing a continuation frame; leaves the current block in a detached state.
    /// Only for continuation manipulation, not direct-style code.
    pub fn call_raw(&mut self, f: Val, args: impl Into<SmallVec<[Val; 3]>>) {
        let args = args.into();
        self.module.replace(
            self.block,
            Node::Fun(Function {
                params: self.params.drain(0..).collect(),
                callee: f,
                call_args: args,
            }),
        );
        self.block = self.module.reserve(None);
    }

    /// Adds a continuation frame which is immediately called with the given arguments, returning the continuation function as well as the arguments.
    /// Only for continuation manipulation, not direct-style code.
    pub fn push_frame(&mut self, args: Vec<(Val, Val)>) -> (Val, Vec<Val>) {
        let callee = self.module.reserve(None);
        let call_args = args.iter().map(|&(x, _)| x).collect();
        let tys: Vec<_> = args.iter().map(|&(_, x)| x).collect();
        self.module.replace(
            self.block,
            Node::Fun(Function {
                params: self.params.drain(0..).collect(),
                callee,
                call_args,
            }),
        );
        self.block = callee;
        self.params.extend(&tys);
        (
            callee,
            tys.iter()
                .enumerate()
                .map(|(i, _)| self.module.add(Node::Param(callee, i as u8), None))
                .collect(),
        )
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

    pub fn binop(&mut self, op: BinOp, a: Val, b: Val) -> Val {
        self.module.add(Node::BinOp(op, a, b), None)
    }

    /// Turns `f (if a then b else c)` into something like:
    /// ```no_test
    /// fun f (x : T) = ...;
    ///
    /// fun _if () = if a b c;
    /// fun _ifcont (x : T) = f x;
    /// fun a () = _ifcont 3;
    /// fun b () = _ifcont 4;
    /// ```
    /// Generated like:
    /// ```no_test
    /// builder.if(a);
    /// b.lower();
    /// builder.otherwise();
    /// c.lower();
    /// let x = builder.endif();
    /// let f = f.lower();
    /// builder.call(f, x);
    /// ```
    /// Returns the argument to the then block. Call `otherwise` afterwards, then `endif`.
    pub fn ifcase(&mut self, case: usize, scrutinee: Val, case_ty: Val) -> Val {
        // At the start of this function (in the example):
        // - self.params is empty
        // - we want self.block to be `_if`

        // Make the call to ifcase: this is `_if`
        let ifcase = self.module.add(Node::IfCase(case, scrutinee), None);
        let yes = self.module.reserve(None);
        let no = self.module.reserve(None);
        self.module.replace(
            self.block,
            Node::Fun(Function {
                params: self.params.drain(0..).collect(),
                callee: ifcase,
                call_args: smallvec![yes, no],
            }),
        );

        // Set up the continuation, `_ifcont`
        let cont = self.module.reserve(None);

        // Now set up generating the true block
        self.block = yes;
        self.params.push(case_ty);
        self.ifs.push((cont, Some(no)));
        self.module.add(Node::Param(yes, 0), None)
    }

    pub fn if_expr(&mut self, cond: Val) {
        // Make the call to ifcase: this is `_if`
        let ifexp = self.module.add(Node::If(cond), None);
        let yes = self.module.reserve(None);
        let no = self.module.reserve(None);
        self.module.replace(
            self.block,
            Node::Fun(Function {
                params: self.params.drain(0..).collect(),
                callee: ifexp,
                call_args: smallvec![yes, no],
            }),
        );

        // Set up the continuation, `_ifcont`
        let cont = self.module.reserve(None);

        // Now set up generating the true block
        self.block = yes;
        self.ifs.push((cont, Some(no)));

        // No parameter since it's a normal if
    }

    /// Switches from the `then` block, which returns the given expressions, to the `else` block.
    pub fn otherwise(&mut self, rets: impl Into<SmallVec<[Val; 3]>>) {
        let (cont, no) = self
            .ifs
            .pop()
            .expect("Called `otherwise` without calling `if` or `ifcase`!");
        let no = no.expect("Called `otherwise` twice in a row!");
        self.ifs.push((cont, None));

        self.module.replace(
            self.block,
            Node::Fun(Function {
                params: self.params.drain(0..).collect(),
                callee: cont,
                call_args: rets.into(),
            }),
        );
        self.block = no;
    }

    /// Ends an `else` block, returning the expressions.
    pub fn endif(&mut self, rets: &[(Val, Val)]) -> Vec<Val> {
        let (cont, no) = self
            .ifs
            .pop()
            .expect("Called `endif` without calling `if` or `ifcase`!");
        if no.is_some() {
            panic!("Called `endif` without calling `otherwise`!");
        }

        let vals = rets.iter().map(|&(x, _)| x).collect();
        self.module.replace(
            self.block,
            Node::Fun(Function {
                params: self.params.drain(0..).collect(),
                callee: cont,
                call_args: vals,
            }),
        );
        self.block = cont;
        let tys = rets.iter().map(|&(_, x)| x);
        self.params.extend(tys);
        rets.iter()
            .enumerate()
            .map(|(i, _)| self.module.add(Node::Param(cont, i as u8), None))
            .collect()
    }

    pub fn type_of(&mut self, x: Val) -> Val {
        let node = self.module.get(x).unwrap().clone();
        if let Node::Param(f, n) = &node {
            let n = *n as usize;
            // It's a parameter of a function that we're in the process of generating, so we have the type stored somewhere
            if self.module.get(*f).is_none() {
                let mut ix = self.funs.len();
                let mut p = self.params.get(n).copied();
                while let Some(i) = ix.checked_sub(1) {
                    if *f == self.funs[i].0 {
                        return p.unwrap();
                    } else {
                        p = self.funs[i].2.get(n).copied();
                    }
                    ix = i;
                }
            }
        }
        node.ty(self.module)
    }

    pub fn project(&mut self, x: Val, i: usize) -> Val {
        self.module.add(Node::Proj(x, i), None)
    }

    pub fn sum_idx(&self, x: Val, i: usize) -> Option<Val> {
        match self.module.get(x) {
            Some(Node::SumType(v)) => Some(v[i]),
            _ => None,
        }
    }

    pub fn unreachable(&mut self, ty: Val) -> Val {
        let ur = self.cons(Constant::Unreachable);
        self.module.replace(
            self.block,
            Node::Fun(Function {
                params: self.params.drain(0..).collect(),
                callee: ur,
                call_args: smallvec![],
            }),
        );
        self.block = self.module.reserve(None);
        self.params.push(ty);
        self.module.add(Node::Param(self.block, 0), None)
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

    pub fn fun_type_multi(&mut self, params: impl Into<SmallVec<[Val; 4]>>, to: Val) -> Val {
        let mut params = params.into();
        let cont_ty = self.module.add(Node::FunType(smallvec![to]), None);
        params.push(cont_ty);
        self.module.add(Node::FunType(params), None)
    }

    pub fn fun_type_raw(&mut self, params: impl Into<SmallVec<[Val; 4]>>) -> Val {
        self.module.add(Node::FunType(params.into()), None)
    }

    pub fn start_pi(&mut self, param: Option<String>, from: Val) -> Pi {
        Pi {
            args: smallvec![self.module.reserve(param)],
            tys: smallvec![from],
        }
    }

    pub fn end_pi(&mut self, pi: Pi, to: Val) -> Val {
        let Pi { args, mut tys } = pi;
        let cont_ty = self.module.add(Node::FunType(smallvec![to]), None);
        tys.push(cont_ty);
        let fun = self.module.add(Node::FunType(tys), None);
        for (i, arg) in args.into_iter().enumerate() {
            self.module.replace(arg, Node::Param(fun, i as u8));
        }
        fun
    }

    pub fn reserve(&mut self, name: Option<String>) -> Val {
        self.module.reserve(name)
    }

    /// Returns the parameter values
    pub fn push_fun(&mut self, params: impl Into<Vec<(Option<String>, Val)>>) -> Vec<Val> {
        let params = params.into();
        let fun = self.module.reserve(None);
        let cont = self.module.add(
            Node::Param(fun, params.len() as u8),
            Some(format!("$cont.return.%{}", fun.num())),
        );
        self.funs.push((fun, self.block, self.params.clone(), cont));
        self.block = fun;
        // Skip adding the continuation parameter and add it later, since we might not know the return type yet
        self.params = params.iter().map(|(_, ty)| *ty).collect();
        params
            .into_iter()
            .enumerate()
            .map(|(i, (name, _))| self.module.add(Node::Param(fun, i as u8), name))
            .collect()
    }

    /// Starts a function without a continuation, returning the parameter values.
    /// Only for continuation manipulation, not direct-style code.
    pub fn push_fun_raw(&mut self, params: impl Into<Vec<(Option<String>, Val)>>) -> Vec<Val> {
        let params = params.into();
        let fun = self.module.reserve(None);
        self.funs
            .push((fun, self.block, self.params.clone(), Val::INVALID));
        self.block = fun;
        self.params = params.iter().map(|(_, ty)| *ty).collect();
        params
            .into_iter()
            .enumerate()
            .map(|(i, (name, _))| self.module.add(Node::Param(fun, i as u8), name))
            .collect()
    }

    /// Ends a function without a continuation by calling another function, returning the created function value.
    /// Like `call_raw` but returns the function instead of leaving it detached.
    /// Only for continuation manipulation, not direct-style code.
    pub fn pop_fun_raw(&mut self, callee: Val, args: impl Into<SmallVec<[Val; 3]>>) -> Val {
        let (fun, block, params, cont) = self.funs.pop().unwrap();
        assert_eq!(
            cont,
            Val::INVALID,
            "Called pop_fun_raw() without push_fun_raw()"
        );

        // We don't use self.call since we don't add the cont parameter here
        self.module.replace(
            self.block,
            Node::Fun(Function {
                params: self.params.drain(0..).collect(),
                callee,
                call_args: args.into(),
            }),
        );
        self.block = block;
        self.params = params;
        fun
    }

    pub fn pop_fun(&mut self, ret: Val, ret_ty: Val) -> Val {
        let (fun, block, params, cont) = self.funs.pop().unwrap();
        assert!(cont != Val::INVALID, "Called pop_fun() with push_fun_raw()");

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

    pub fn pop_fun_multi(&mut self, rets: Vec<(Val, Val)>) -> Val {
        let (fun, block, params, cont) = self.funs.pop().unwrap();
        assert!(
            cont != Val::INVALID,
            "Called pop_fun_multi() with push_fun_raw()"
        );

        // Add the continuation parameter to the function
        let tys = rets.iter().map(|&(_, ty)| ty).collect();
        let cont_ty = self.module.add(Node::FunType(tys), None);
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
        let vals = rets.iter().map(|&(val, _)| val).collect();
        self.module.replace(
            self.block,
            Node::Fun(Function {
                params: self.params.drain(0..).collect(),
                callee: cont,
                call_args: vals,
            }),
        );
        self.block = block;
        self.params = params;
        fun
    }

    pub fn extern_declare(
        &mut self,
        name: String,
        params: impl Into<SmallVec<[Val; 3]>>,
        ret: Val,
    ) -> Val {
        self.module.add(
            Node::ExternFun(name.clone(), params.into(), ret),
            Some(name),
        )
    }

    pub fn extern_call(&mut self, f: Val, args: impl Into<SmallVec<[Val; 3]>>) -> Val {
        let cont = self.module.reserve(None);
        let mut args = args.into();
        args.push(cont);
        let callee = self.module.add(Node::ExternCall(f), None);
        self.module.replace(
            self.block,
            Node::Fun(Function {
                params: self.params.drain(0..).collect(),
                callee,
                call_args: args,
            }),
        );
        self.block = cont;
        let ret_ty = match f.get(self.module).clone().ty(self.module).get(self.module) {
            Node::ExternFunType(_, r) => *r,
            _ => panic!("extern_call() requires extern fun!"),
        };
        self.params.push(ret_ty);
        self.module.add(Node::Param(cont, 0), None)
    }

    pub fn ref_type(&mut self, inner_ty: Val) -> Val {
        self.module.add(Node::RefTy(inner_ty), None)
    }

    pub fn refnew(&mut self, inner_ty: Val) -> Val {
        let cont = self.module.reserve(None);
        let callee = self.module.add(Node::Ref(RefOp::RefNew(inner_ty)), None);
        self.module.replace(
            self.block,
            Node::Fun(Function {
                params: self.params.drain(0..).collect(),
                callee,
                call_args: smallvec![cont],
            }),
        );
        self.block = cont;
        let ret_ty = self.module.add(Node::RefTy(inner_ty), None);
        self.params.push(ret_ty);
        self.module.add(Node::Param(cont, 0), None)
    }

    pub fn refget(&mut self, vref: Val) -> Val {
        let cont = self.module.reserve(None);
        let callee = self.module.add(Node::Ref(RefOp::RefGet(vref)), None);
        self.module.replace(
            self.block,
            Node::Fun(Function {
                params: self.params.drain(0..).collect(),
                callee,
                call_args: smallvec![cont],
            }),
        );
        self.block = cont;
        let ret_ty = match vref
            .get(self.module)
            .clone()
            .ty(self.module)
            .get(self.module)
        {
            Node::RefTy(r) => *r,
            _ => panic!("refget() requires ref value!"),
        };
        self.params.push(ret_ty);
        self.module.add(Node::Param(cont, 0), None)
    }

    pub fn refset(&mut self, vref: Val, new_val: Val) {
        let cont = self.module.reserve(None);
        let callee = self
            .module
            .add(Node::Ref(RefOp::RefSet(vref, new_val)), None);
        self.module.replace(
            self.block,
            Node::Fun(Function {
                params: self.params.drain(0..).collect(),
                callee,
                call_args: smallvec![cont],
            }),
        );
        self.block = cont;
        // No return value from `refset`
    }
}
