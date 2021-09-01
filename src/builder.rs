use crate::ir::*;
use smallvec::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BuildState {
    pub block: Val,
    params: Vec<Val>,
}

/// Takes care of the transformation from direct style to CPS.
pub struct Builder<'m> {
    module: &'m mut Module,
    block: Val,
    params: Vec<Val>,
    /// (fun, block, params, cont)
    funs: Vec<(Val, Val, Vec<Val>, Option<Val>)>,
    /// (continuation, else block)
    ifs: Vec<(Val, Option<Val>)>,
}
impl<'m> Builder<'m> {
    pub fn new(m: &'m mut Module, state: Option<BuildState>) -> Self {
        let (block, params) = match state {
            Some(BuildState { block, params }) => (block, params),
            None => (m.reserve(None), Vec::new()),
        };
        Builder {
            module: m,
            block,
            params,
            funs: Vec::new(),
            ifs: Vec::new(),
        }
    }

    pub fn state(&self) -> BuildState {
        BuildState {
            block: self.block,
            params: self.params.clone(),
        }
    }

    pub fn stop(&mut self) {
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

    pub fn binop(&mut self, op: BinOp, signed: bool, a: Val, b: Val) -> Val {
        self.module.add(Node::BinOp(op, signed, a, b), None)
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
        let node = self.module.slots().node(x).unwrap().clone();
        if let Node::Param(f, n) = &node {
            let n = *n as usize;
            // It's a parameter of a function that we're in the process of generating, so we have the type stored somewhere
            if self.module.slots().node(*f).is_none() {
                if *f == self.block {
                    return self.params[n];
                }
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
        let ty = self.type_of(x);
        self.module.add(Node::Proj(ty, x, i), None)
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

    /// `nargs` is the number of function arguments, plus one for the continuation
    pub fn fun_type(&mut self, nargs: usize) -> Val {
        self.module.add(Node::FunType(nargs), None)
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
            Some(format!("$cont.return.%{}", fun.id())),
        );
        self.funs
            .push((fun, self.block, self.params.clone(), Some(cont)));
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
        self.funs.push((fun, self.block, self.params.clone(), None));
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
        assert!(
            cont.is_none(),
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

    pub fn pop_fun(&mut self, ret: Val) -> Val {
        let (fun, block, params, cont) = self.funs.pop().unwrap();
        let cont = cont.expect("Called pop_fun() with push_fun_raw()");

        // Add the continuation parameter to the function
        let cont_ty = self.module.add(Node::FunType(1), None);
        let funv = self.module.unredirect(fun);
        match self.module.world.write_storage::<Slot>().get_mut(funv) {
            Some(Slot::Full(Node::Fun(f))) => {
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
        let ret_ty = match self.type_of(f).get(&self.module.slots()) {
            Node::ExternFunType(_, r) => *r,
            _ => panic!("extern_call() requires extern fun!"),
        };

        let cont = self.module.reserve(None);
        let mut args = args.into();
        args.push(cont);
        let callee = self.module.add(Node::ExternCall(f, ret_ty), None);
        self.module.replace(
            self.block,
            Node::Fun(Function {
                params: self.params.drain(0..).collect(),
                callee,
                call_args: args,
            }),
        );
        self.block = cont;
        self.params.push(ret_ty);
        self.module.add(Node::Param(cont, 0), None)
    }

    pub fn unbox(&mut self, inner_ty: Val) -> Val {
        self.module.add(Node::Unbox(inner_ty), None)
    }

    pub fn ref_type(&mut self, inner_ty: Val) -> Val {
        self.module.add(Node::RefTy(inner_ty), None)
    }

    pub fn refnew(&mut self, inner_ty: Val) -> Val {
        let cont = self.module.reserve(None);
        let callee = self.module.add(Node::Ref(inner_ty, RefOp::RefNew), None);
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
        let ret_ty = match self.type_of(vref).get(&self.module.slots()) {
            Node::RefTy(r) => *r,
            _ => panic!("refget() requires ref value!"),
        };

        let cont = self.module.reserve(None);
        let callee = self
            .module
            .add(Node::Ref(ret_ty, RefOp::RefGet(vref)), None);
        self.module.replace(
            self.block,
            Node::Fun(Function {
                params: self.params.drain(0..).collect(),
                callee,
                call_args: smallvec![cont],
            }),
        );
        self.block = cont;
        self.params.push(ret_ty);
        self.module.add(Node::Param(cont, 0), None)
    }

    pub fn refset(&mut self, vref: Val, new_val: Val) {
        let inner_ty = match self.type_of(vref).get(&self.module.slots()) {
            Node::RefTy(r) => *r,
            _ => panic!("refget() requires ref value!"),
        };

        let cont = self.module.reserve(None);
        let callee = self
            .module
            .add(Node::Ref(inner_ty, RefOp::RefSet(vref, new_val)), None);
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
