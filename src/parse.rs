use smallvec::{smallvec, SmallVec};

use crate::ir::*;
use std::collections::HashMap;
use std::iter::Peekable;
use std::str::Chars;

/// We only do one pass, so the parser includes name resolution.
pub struct Parser<'a> {
    chars: Peekable<Chars<'a>>,
    input: &'a str,
    pos: usize,
    module: Module,
    names: HashMap<&'a str, (Val, usize)>,
}

impl<'a> Parser<'a> {
    /// This implements a basic version of what rustc or clang error messages look like
    fn error(&self, message: impl Into<String>) -> ! {
        let mut lnum = 0;
        let mut lpos = 0;
        let line = self
            .input
            .lines()
            .find(|x| {
                // +1 for the \n
                if lpos + x.len() + 1 > self.pos {
                    true
                } else {
                    lnum += 1;
                    lpos += x.len() + 1;
                    false
                }
            })
            .unwrap();
        let col = self.pos - lpos;
        eprintln!("Syntax error: {}", message.into());
        eprintln!("    --> {}:{}", lnum, col);
        eprintln!("     |");
        eprintln!("{:4} | {}", lnum, line);
        eprintln!("     | {:>width$}", "^", width = col + 1);
        panic!("Syntax error")
    }

    pub fn new(input: &'a str) -> Self {
        Parser {
            chars: input.chars().peekable(),
            input,
            pos: 0,
            module: Module::new(),
            names: Default::default(),
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().copied()
    }

    fn next(&mut self) -> Option<char> {
        let c = self.chars.next()?;
        self.pos += c.len_utf8();
        Some(c)
    }

    /// If the next thing is `s`, consumes it and returns `true`, otherwise returns `false`.
    fn matches(&mut self, s: &str) -> bool {
        if self.input[self.pos..].starts_with(s) {
            for _ in s.chars() {
                self.next();
            }
            true
        } else {
            false
        }
    }

    /// Consumes `s`, panicking if it doesn't match
    fn expect(&mut self, s: &str) {
        if !self.matches(s) {
            self.error(format!("Expected {:?}", s))
        }
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            if c.is_whitespace() {
                self.next();
            } else if c == '#' {
                // Skip line comments
                while self.peek() != Some('\n') {
                    self.next();
                }
            } else {
                break;
            }
        }
    }

    fn name(&mut self) -> &'a str {
        let start = self.pos;
        while let Some(c) = self.peek() {
            // Durin allows all non-whitespace characters in names, except "(", ")", and certain binary operators, since those are ambiguous
            if !c.is_whitespace()
                && c != '('
                && c != ')'
                && c != ':'
                && c != ','
                && c != ';'
                && c != '|'
                && c != '.'
            {
                self.next();
            } else {
                break;
            }
        }
        if self.pos == start {
            self.error("Expected name".to_string())
        }
        &self.input[start..self.pos]
    }

    fn var(&mut self) -> Val {
        let pos = self.pos;
        let name = self.name();
        match self.names.get(name) {
            Some(&(x, _)) => x,
            // We implicitly forward-declare variables we can't find (like C), then add their definitions later
            // If we get to the end of the file and a variable hasn't been defined, we give an error
            None => self.declare_name(name, pos),
        }
    }

    fn declare_name(&mut self, name: &'a str, pos: usize) -> Val {
        let v = self.module.reserve(Some(name.to_owned()));
        self.names.insert(name, (v, pos));
        v
    }

    /// Basically the same operators as Pika are (will be) supported
    fn binop(&mut self) -> Option<BinOp> {
        Some(match self.peek()? {
            '=' if self.matches("==") => BinOp::Eq,
            '!' if self.matches("!=") => BinOp::NEq,
            '*' if self.matches("**") => self.error("Exponentiation not supported yet"),
            '*' => {
                self.next();
                BinOp::Mul
            }
            '%' => {
                self.next();
                BinOp::Mod
            }
            '+' => {
                self.next();
                BinOp::Add
            }
            '-' => {
                self.next();
                BinOp::Sub
            }
            '/' => {
                self.next();
                BinOp::Div
            }
            '<' => {
                if self.matches("<=") {
                    BinOp::Leq
                } else {
                    self.next();
                    BinOp::Lt
                }
            }
            '>' => {
                if self.matches(">=") {
                    BinOp::Geq
                } else {
                    self.next();
                    BinOp::Gt
                }
            }
            _ => return None,
        })
    }

    fn atom(&mut self, ty: Option<Val>) -> Val {
        if self.matches("{") {
            self.skip_whitespace();

            let mut v: SmallVec<[Val; 3]> = SmallVec::new();
            while !self.matches("}") {
                self.skip_whitespace();
                v.push(self.expr());
                self.skip_whitespace();
                if self.matches("}") {
                    break;
                } else {
                    self.expect(",");
                }
            }

            self.skip_whitespace();
            let ty = if self.matches("of") {
                self.skip_whitespace();

                self.atom(None)
            } else {
                if let Some(ty) = ty {
                    ty
                } else {
                    self.error("type annotation required here")
                }
            };

            self.module.add(Node::Product(ty, v), None)
        } else if self.matches("sig") {
            self.skip_whitespace();
            self.expect("{");
            self.skip_whitespace();

            let mut tys = SmallVec::new();
            let mut names = Vec::new();
            while !self.matches("}") {
                tys.push(self.expr());
                self.skip_whitespace();

                let name = match self.peek().unwrap_or_else(|| self.error("expected '}'")) {
                    ',' | '}' => self.declare_name("_", self.pos),
                    _ => {
                        let pos = self.pos;
                        let name = self.name();
                        self.declare_name(name, pos)
                    }
                };
                self.skip_whitespace();
                names.push(name);

                if self.matches("}") {
                    break;
                } else {
                    self.expect(",");
                    self.skip_whitespace();
                }
            }
            let t = self.module.add(Node::ProdType(tys), None);
            for (i, x) in names.into_iter().enumerate() {
                self.module.replace(x, Node::Param(t, i as u8));
            }
            t
        } else if self.matches("(") {
            // A binop
            let expr = self.expr();
            self.expect(")");
            expr
        } else if self.matches("fun") {
            self.skip_whitespace();

            let mut i = String::new();
            while self.peek().expect("unexpected EOF").is_digit(10) {
                i.push(self.next().unwrap());
            }
            let i = i.parse().expect("invalid number for ifcase tag");
            self.skip_whitespace();

            self.module.add(Node::FunType(i), None)
        } else if self.matches("Type") {
            self.module.add(Node::Const(Constant::TypeType), None)
        } else if self.matches("I32") {
            self.module
                .add(Node::Const(Constant::IntType(Width::W32)), None)
        } else if self.matches("I64") {
            self.module
                .add(Node::Const(Constant::IntType(Width::W64)), None)
        } else if self.matches("I1") {
            self.module
                .add(Node::Const(Constant::IntType(Width::W1)), None)
        } else if self.matches("I8") {
            self.module
                .add(Node::Const(Constant::IntType(Width::W8)), None)
        } else if self.matches("I16") {
            self.module
                .add(Node::Const(Constant::IntType(Width::W16)), None)
        } else if self.matches("ref") {
            self.skip_whitespace();
            let ty = self.expr();
            self.module.add(Node::RefTy(ty), None)
        } else if self
            .peek()
            .expect("unexpected EOF, maybe missing close parenthesis")
            .is_digit(10)
            || self.peek().unwrap() == '-'
        {
            let mut s = String::new();
            while self.peek().unwrap().is_digit(10) || self.peek().unwrap() == '-' {
                s.push(self.next().unwrap());
            }
            // } else {
            //     self.error("Expected int width suffix: one of i1, i8, i16, i32, i64");
            // }
            let w = if self.matches("i") {
                match () {
                    _ if self.matches("64") => Width::W64,
                    _ if self.matches("32") => Width::W32,
                    _ if self.matches("16") => Width::W16,
                    _ if self.matches("8") => Width::W8,
                    _ if self.matches("1") => Width::W1,
                    _ => self.error("Expected int width suffix: one of i1, i8, i16, i32, i64"),
                }
            } else {
                ty.and_then(|x| {
                    self.module
                        .slots()
                        .node(x)
                        .and_then(|x| {
                            if let Node::Const(Constant::IntType(w)) = x {
                                Some(w)
                            } else {
                                None
                            }
                        })
                        .copied()
                })
                .unwrap_or_else(|| {
                    self.error("expected int width suffix: one of i1, i8, i16, i32, i64")
                })
            };
            use std::str::FromStr;
            let i = i64::from_str(&s).unwrap_or_else(|e| self.error(format!("{}", e)));
            self.module.add(Node::Const(Constant::Int(w, i)), None)
        } else {
            self.var()
        }
    }

    fn expr(&mut self) -> Val {
        // A binop
        let lhs = self.atom(None);
        self.skip_whitespace();
        if self.matches("|") {
            // Sum type
            let mut v = smallvec![lhs];
            loop {
                self.skip_whitespace();
                let next = self.atom(None);
                v.push(next);
                self.skip_whitespace();
                if self.matches("|") {
                    continue;
                } else {
                    break;
                }
            }
            self.module.add(Node::SumType(v), None)
        } else if self.matches(".") {
            // Projection of a product type member
            self.skip_whitespace();
            let mut i = String::new();
            while self.peek().expect("unexpected EOF").is_digit(10) {
                i.push(self.next().unwrap());
            }
            let i: usize = i.parse().expect("invalid number for ifcase tag");
            self.skip_whitespace();
            self.expect("of");
            self.skip_whitespace();
            let ty = self.atom(None);
            self.skip_whitespace();
            self.module.add(Node::Proj(ty, lhs, i), None)
        } else if self.matches(":") {
            // Injection into a sum type
            self.skip_whitespace();
            let mut i = String::new();
            while self.peek().expect("unexpected EOF").is_digit(10) {
                i.push(self.next().unwrap());
            }
            let i: usize = i
                .parse()
                .unwrap_or_else(|_| self.error("invalid number for ifcase tag"));
            self.skip_whitespace();
            let val_ty = self
                .module
                .slots()
                .node(lhs)
                .and_then(|x| {
                    if let Node::SumType(v) = x {
                        Some(v)
                    } else {
                        None
                    }
                })
                .and_then(|x| x.get(i))
                .copied();
            let val = self.atom(val_ty);
            self.skip_whitespace();
            self.module.add(Node::Inj(lhs, i, val), None)
        } else if let Some(op) = self.binop() {
            self.skip_whitespace();
            let rhs = self.atom(None);
            self.skip_whitespace();
            self.module.add(Node::BinOp(op, true, lhs, rhs), None)
        } else {
            lhs
        }
    }

    pub fn parse(mut self) -> Module {
        loop {
            self.skip_whitespace();
            if self.peek().is_none() {
                break;
            }

            if self.matches("val") {
                // Parse a local
                self.skip_whitespace();
                let name = self.name();
                // Vals can be forward-declared too
                let val = self
                    .names
                    .get(name)
                    .filter(|&&(x, _)| self.module.slots().node(x).is_none())
                    .map(|&(x, _)| x)
                    .unwrap_or_else(|| {
                        let v = self.module.reserve(Some(name.to_owned()));
                        self.names.insert(name, (v, self.pos));
                        v
                    });
                self.skip_whitespace();
                self.expect("=");
                self.skip_whitespace();
                let val2 = self.expr();
                self.module.redirect(val, val2);
                self.skip_whitespace();
                continue;
            } else if self.matches("extern") {
                // Parse an extern function declaration
                self.skip_whitespace();
                self.expect("fun");
                self.skip_whitespace();

                let name = self.name();
                let val = self
                    .names
                    .get(name)
                    .filter(|&&(x, _)| self.module.slots().node(x).is_none())
                    .map(|&(x, _)| x)
                    .unwrap_or_else(|| {
                        let v = self.module.reserve(Some(name.to_owned()));
                        self.names.insert(name, (v, self.pos));
                        v
                    });
                self.skip_whitespace();

                let mut params = SmallVec::new();
                // Arguments are optional, if present look like `(x : I32, y : fun)`
                if self.matches("(") {
                    self.skip_whitespace();
                    while !self.matches(")") {
                        let name = self.name();
                        self.skip_whitespace();
                        self.expect(":");
                        self.skip_whitespace();
                        let ty = self.expr();
                        self.skip_whitespace();

                        let i = params.len();
                        let val = self
                            .module
                            .add(Node::Param(val, i as _), Some(name.to_owned()));
                        self.names.insert(name, (val, self.pos));
                        params.push(ty);
                        if self.matches(")") {
                            break;
                        } else {
                            self.expect(",");
                            self.skip_whitespace();
                        }
                    }
                    self.skip_whitespace();
                }

                self.expect(":");
                self.skip_whitespace();
                let ret_ty = self.expr();
                self.skip_whitespace();

                self.module
                    .replace(val, Node::ExternFun(name.into(), params, ret_ty));
                continue;
            }

            // Parse a function
            self.expect("fun");
            self.skip_whitespace();

            let name = self.name();
            self.skip_whitespace();
            // Functions can be recursive
            let val = self
                .names
                .get(name)
                .filter(|&&(x, _)| self.module.slots().node(x).is_none())
                .map(|&(x, _)| x)
                .unwrap_or_else(|| {
                    let v = self.module.reserve(Some(name.to_owned()));
                    self.names.insert(name, (v, self.pos));
                    v
                });

            let mut params = SmallVec::new();
            // Arguments are optional, if present look like `(x : I32, y : fun)`
            if self.matches("(") {
                self.skip_whitespace();
                while !self.matches(")") {
                    let name = self.name();
                    self.skip_whitespace();
                    self.expect(":");
                    self.skip_whitespace();
                    let ty = self.expr();
                    self.skip_whitespace();

                    let i = params.len();
                    let val = self
                        .module
                        .add(Node::Param(val, i as _), Some(name.to_owned()));
                    self.names.insert(name, (val, self.pos));
                    params.push(ty);
                    if self.matches(")") {
                        break;
                    } else {
                        self.expect(",");
                        self.skip_whitespace();
                    }
                }
                self.skip_whitespace();
            }

            self.expect("=");
            self.skip_whitespace();

            if self.matches("ifcase") {
                self.skip_whitespace();
                let mut i = String::new();
                while self.peek().expect("unexpected EOF").is_digit(10) {
                    i.push(self.next().unwrap());
                }
                let i: usize = i.parse().expect("invalid number for ifcase tag");
                self.skip_whitespace();

                let x = self.expr();
                self.skip_whitespace();

                let fthen = self.expr();
                self.skip_whitespace();

                let felse = self.expr();
                self.skip_whitespace();

                let callee = self.module.add(Node::IfCase(i, x), None);
                self.module.replace(
                    val,
                    Node::Fun(Function {
                        params,
                        callee,
                        call_args: smallvec![fthen, felse],
                    }),
                );
            // Do ifcase first since `if` would match `ifcase` too
            } else if self.matches("if") {
                self.skip_whitespace();

                let x = self.expr();
                self.skip_whitespace();

                let fthen = self.expr();
                self.skip_whitespace();

                let felse = self.expr();
                self.skip_whitespace();

                let callee = self.module.add(Node::If(x), None);
                self.module.replace(
                    val,
                    Node::Fun(Function {
                        params,
                        callee,
                        call_args: smallvec![fthen, felse],
                    }),
                );
            } else if self.matches("unreachable") {
                self.skip_whitespace();
                let callee = self.module.add(Node::Const(Constant::Unreachable), None);
                self.module.replace(
                    val,
                    Node::Fun(Function {
                        params,
                        callee,
                        call_args: SmallVec::new(),
                    }),
                );
            } else if self.matches("stop") {
                self.skip_whitespace();
                let callee = self.module.add(Node::Const(Constant::Stop), None);
                self.module.replace(
                    val,
                    Node::Fun(Function {
                        params,
                        callee,
                        call_args: SmallVec::new(),
                    }),
                );
            } else if self.matches("refnew") {
                self.skip_whitespace();

                let ty = self.expr();
                self.skip_whitespace();

                let cont = self.expr();
                self.skip_whitespace();

                let callee = self.module.add(Node::Ref(ty, RefOp::RefNew), None);
                self.module.replace(
                    val,
                    Node::Fun(Function {
                        params,
                        callee,
                        call_args: smallvec![cont],
                    }),
                );
            } else if self.matches("refset") {
                self.skip_whitespace();

                let ty = self.expr();
                self.skip_whitespace();

                let ptr = self.expr();
                self.skip_whitespace();

                let v = self.expr();
                self.skip_whitespace();

                let cont = self.expr();
                self.skip_whitespace();

                let callee = self.module.add(Node::Ref(ty, RefOp::RefSet(ptr, v)), None);
                self.module.replace(
                    val,
                    Node::Fun(Function {
                        params,
                        callee,
                        call_args: smallvec![cont],
                    }),
                );
            } else if self.matches("refget") {
                self.skip_whitespace();

                let ty = self.expr();
                self.skip_whitespace();

                let ptr = self.expr();
                self.skip_whitespace();

                let cont = self.expr();
                self.skip_whitespace();

                let callee = self.module.add(Node::Ref(ty, RefOp::RefGet(ptr)), None);
                self.module.replace(
                    val,
                    Node::Fun(Function {
                        params,
                        callee,
                        call_args: smallvec![cont],
                    }),
                );
            } else if self.matches("externcall") {
                self.skip_whitespace();

                let ret_ty = self.atom(None);
                self.skip_whitespace();

                let x = self.atom(None);
                self.skip_whitespace();

                let mut call_args = SmallVec::new();
                self.expect("(");
                if !self.matches(")") {
                    loop {
                        call_args.push(self.expr());
                        self.skip_whitespace();
                        if !self.matches(")") {
                            self.expect(",");
                            self.skip_whitespace();
                        } else {
                            break;
                        }
                    }
                }

                let callee = self.module.add(Node::ExternCall(x, ret_ty), None);
                self.module.replace(
                    val,
                    Node::Fun(Function {
                        params,
                        callee,
                        call_args,
                    }),
                )
            } else if self.matches("call") {
                self.skip_whitespace();

                let callee = self.expr();
                self.skip_whitespace();

                let mut call_args = SmallVec::new();
                self.expect("(");
                if !self.matches(")") {
                    loop {
                        call_args.push(self.expr());
                        self.skip_whitespace();
                        if !self.matches(")") {
                            self.expect(",");
                            self.skip_whitespace();
                        } else {
                            break;
                        }
                    }
                }

                self.module.replace(
                    val,
                    Node::Fun(Function {
                        params,
                        callee,
                        call_args,
                    }),
                )
            } else {
                self.error("expected instruction (e.g. 'call' or 'stop')");
            }
        }

        for (name, (val, pos)) in &self.names {
            if self.module.slots().node(*val).is_none() {
                self.pos = *pos;
                self.error(format!("Name '{}' not found", name));
            }
        }

        self.module
    }
}
