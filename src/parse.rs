use smallvec::SmallVec;

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
                if lpos + x.len() > self.pos {
                    true
                } else {
                    lnum += 1;
                    lpos += x.len();
                    false
                }
            })
            .unwrap();
        let col = self.pos - lpos;
        eprintln!("Syntax error: {}", message.into());
        eprintln!("    --> {}:{}", lnum, col);
        eprintln!("     |");
        eprintln!("{:4} | {}", lnum, line);
        eprintln!("     | {:>width$}", "^", width = col - 1);
        panic!("Syntax error")
    }

    pub fn new(input: &'a str) -> Self {
        Parser {
            chars: input.chars().peekable(),
            input,
            pos: 0,
            module: Default::default(),
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
            } else {
                break;
            }
        }
    }

    fn name(&mut self) -> &'a str {
        let start = self.pos;
        while let Some(c) = self.peek() {
            // Durin allows all non-whitespace characters in names, except "(", ")", ":", ";", and ",", since those are ambiguous
            if !c.is_whitespace() && c != '(' && c != ')' && c != ':' && c != ',' && c != ';' {
                self.next();
            } else {
                break;
            }
        }
        if self.pos == start {
            self.pos = start;
            self.error(format!("Expected name"))
        }
        &self.input[start..self.pos]
    }

    fn var(&mut self) -> Val {
        let name = self.name();
        match self.names.get(name) {
            Some(&(x, _)) => x,
            None => {
                let v = self.module.reserve(Some(name.to_owned()));
                self.names.insert(name, (v, self.pos));
                v
            } // panic!("Name '{}' not found at position {}", name, self.pos),
        }
    }

    /// Basically the same operators as Pika are (will be) supported
    fn binop(&mut self) -> BinOp {
        match self.peek().unwrap() {
            '=' if self.matches("==") => BinOp::IEq,
            '*' if self.matches("**") => self.error("Exponentiation not supported yet"),
            '*' => {
                self.next();
                BinOp::IMul
            }
            '+' => {
                self.next();
                BinOp::IAdd
            }
            '-' => {
                self.next();
                BinOp::ISub
            }
            '/' => {
                self.next();
                BinOp::IDiv
            }
            _ => self.error("Expected operator"),
        }
    }

    fn expr(&mut self) -> Val {
        if self.matches("(") {
            // A binop
            let lhs = self.expr();
            self.skip_whitespace();
            let op = self.binop();
            self.skip_whitespace();
            let rhs = self.expr();
            self.skip_whitespace();
            self.expect(")");
            self.module.add(Node::BinOp(op, lhs, rhs), None)
        } else if self.matches("fun") {
            self.module.add(Node::Const(Constant::FunType), None)
        } else if self.matches("I32") {
            self.module
                .add(Node::Const(Constant::IntType(Width::W32)), None)
        } else if self.peek().unwrap().is_digit(10) || self.peek().unwrap() == '-' {
            let mut s = String::new();
            while self.peek().unwrap() != 'i' {
                if self.peek().unwrap().is_digit(10) || self.peek().unwrap() == '-' {
                    s.push(self.next().unwrap());
                } else {
                    self.error("Expected int width suffix: one of i1, i8, i16, i32, i64");
                }
            }
            self.next();
            let w = match () {
                _ if self.matches("64") => Width::W64,
                _ if self.matches("32") => Width::W32,
                _ if self.matches("16") => Width::W16,
                _ if self.matches("8") => Width::W8,
                _ if self.matches("1") => Width::W1,
                _ => self.error("Expected int width suffix: one of i1, i8, i16, i32, i64"),
            };
            use std::str::FromStr;
            let i = i64::from_str(&s).unwrap_or_else(|e| self.error(format!("{}", e)));
            self.module.add(Node::Const(Constant::Int(w, i)), None)
        } else {
            self.var()
        }
    }

    pub fn parse(mut self) -> Module {
        loop {
            self.skip_whitespace();
            if self.peek().is_none() {
                break;
            }
            self.expect("fun");
            self.skip_whitespace();

            let name = self.name();
            self.skip_whitespace();
            // Functions can be recursive
            let val = self
                .names
                .get(name)
                .filter(|&&(x, _)| self.module.get(x).is_none())
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

            let callee = self.var();
            self.skip_whitespace();

            let mut call_args = SmallVec::new();
            while !self.matches(";") {
                call_args.push(self.expr());
                self.skip_whitespace();
            }

            self.module.replace(
                val,
                Node::Fun(Function {
                    params,
                    callee,
                    call_args,
                }),
            )
        }

        for (name, (val, pos)) in &self.names {
            if self.module.get(*val).is_none() {
                self.pos = *pos;
                self.error(format!("Name '{}' not found", name));
            }
        }

        self.module
    }
}
