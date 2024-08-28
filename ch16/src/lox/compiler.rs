use std::{mem::Discriminant, path::Display};

use crate::lox::scanner::{Scanner, TokenType};

pub struct Compiler<'a> {
    scanner: Scanner<'a>,
}

impl<'a> Compiler<'a> {
    pub fn new(source: &'a str) -> Self {
        Self { scanner: Scanner::new(source) }
    }

    pub fn compile(&mut self) {
        let mut line = usize::MAX;
        loop {
            if let Ok(token) = self.scanner.scan_token() {
                if token.line != line {
                    print!("{:4}", token.line);
                    line = token.line;
                } else {
                    print!("   | ");
                }
                println!("{:?} '{}'", token.token_type, token.lexeme);

                if token.token_type == TokenType::Eof {
                    break;
                }
            } else {
                println!("Error scanning token");
                break;
            }
        }
    }
}
