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
            panic!("Expected {:?} at position {}", s, self.pos)
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
            // Durin allows all non-whitespace characters in names, except ")", ":", ";", and ",", since those are ambiguous
            if !c.is_whitespace() && c != ')' && c != ':' && c != ',' && c != ';' {
                self.next();
            } else {
                break;
            }
        }
        if self.pos == start {
            panic!("Expected name at position {}", start)
        }
        &self.input[start..self.pos]
    }

    fn var(&mut self) -> Val {
        let name = self.name();
        match self.names.get(name) {
            Some(&(x, _)) => x,
            None => {
                let v = self.module.reserve();
                self.names.insert(name, (v, self.pos));
                v
            } // panic!("Name '{}' not found at position {}", name, self.pos),
        }
    }

    fn expr(&mut self) -> Val {
        if self.matches("fun") {
            self.module.add(Node::Const(Constant::FunType))
        } else if self.matches("I32") {
            self.module.add(Node::Const(Constant::IntType(Width::W32)))
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
            let val = self.names.get(name).map(|&(x, _)| x).unwrap_or_else(|| {
                let v = self.module.reserve();
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
                    let val = self.module.add(Node::Param(val, i as _));
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
                call_args.push(self.var());
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

        for (name, (val, pos)) in self.names {
            if self.module.get(val).is_none() {
                panic!("Name '{}' not found at position {}", name, pos);
            }
        }

        self.module
    }
}
