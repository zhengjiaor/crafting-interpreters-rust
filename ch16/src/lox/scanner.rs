use std::fmt::{Debug, Display};

use anyhow::Result;
use thiserror::Error;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenType {
    // Single-character tokens.
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Comma,
    Dot,
    Minus,
    Plus,
    Semicolon,
    Slash,
    Star,

    // One or two character tokens.
    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,

    // Literals.
    Identifier,
    String,
    Number,

    // Keywords.
    And,
    Class,
    Else,
    False,
    Fun,
    For,
    If,
    Nil,
    Or,
    Print,
    Return,
    Super,
    This,
    True,
    Var,
    While,

    Error,
    Eof,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token<'a> {
    pub token_type: TokenType,
    pub lexeme: &'a str,
    pub line: usize,
}

#[derive(Error, Debug)]
#[error("Scan error: {message} at line {line}")]
pub struct ScanError {
    message: &'static str,
    line: usize,
}

pub struct Scanner<'a> {
    source: &'a str,
    start: usize,
    current: usize,
    line: usize,
}

impl<'a> Scanner<'a> {
    pub fn new(source: &'a str) -> Self {
        Self { source, start: 0, current: 0, line: 1 }
    }

    pub fn scan_token(&mut self) -> Result<Token> {
        self.skip_white_spaces();
        self.start = self.current;

        if self.is_at_end() {
            return self.make_token(TokenType::Eof);
        }

        let c = self.advance();

        match c {
            b'(' => return self.make_token(TokenType::LeftParen),
            b')' => return self.make_token(TokenType::RightParen),
            b'{' => return self.make_token(TokenType::LeftBrace),
            b'}' => return self.make_token(TokenType::RightBrace),
            b';' => return self.make_token(TokenType::Semicolon),
            b',' => return self.make_token(TokenType::Comma),
            b'.' => return self.make_token(TokenType::Dot),
            b'-' => return self.make_token(TokenType::Minus),
            b'+' => return self.make_token(TokenType::Plus),
            b'/' => return self.make_token(TokenType::Slash),
            b'*' => return self.make_token(TokenType::Star),
            b'!' => {
                if self.match_byte(b'=') {
                    return self.make_token(TokenType::BangEqual);
                } else {
                    return self.make_token(TokenType::Bang);
                }
            }
            b'=' => {
                if self.match_byte(b'=') {
                    return self.make_token(TokenType::EqualEqual);
                } else {
                    return self.make_token(TokenType::Equal);
                }
            }
            b'<' => {
                if self.match_byte(b'=') {
                    return self.make_token(TokenType::LessEqual);
                } else {
                    return self.make_token(TokenType::Less);
                }
            }
            b'>' => {
                if self.match_byte(b'=') {
                    return self.make_token(TokenType::GreaterEqual);
                } else {
                    return self.make_token(TokenType::Greater);
                }
            }
            b'"' => return self.string(),
            b'0'..=b'9' => return self.number(),
            _ if Self::is_alpha(c) => return self.identifier(),
            _ => self.error("Unexpected character"),
        }
    }

    fn skip_white_spaces(&mut self) {
        loop {
            let c = self.peek();
            match c {
                b' ' | b'\r' | b'\t' => {
                    self.advance();
                }
                b'/' => {
                    if self.peek_next() == b'/' {
                        while !self.is_at_end() && self.peek() != b'\n' {
                            self.advance();
                        }
                    }
                }
                b'\n' => {
                    self.line += 1;
                    self.advance();
                }
                _ => return,
            }
        }
    }

    fn peek(&self) -> u8 {
        if self.is_at_end() {
            b'\0'
        } else {
            self.source.as_bytes()[self.current]
        }
    }

    fn peek_next(&self) -> u8 {
        if self.current + 1 >= self.source.len() {
            b'\0'
        } else {
            self.source.as_bytes()[self.current + 1]
        }
    }

    fn is_at_end(&self) -> bool {
        self.current >= self.source.len()
    }

    fn make_token(&self, token_type: TokenType) -> Result<Token<'a>> {
        Ok(Token { token_type, lexeme: &self.source[self.start..self.current], line: self.line })
    }

    fn error(&self, message: &'static str) -> Result<Token<'a>> {
        Err(ScanError { message, line: self.line }.into())
    }

    fn advance(&mut self) -> u8 {
        self.current += 1;
        self.source.as_bytes()[self.current - 1]
    }

    fn match_byte(&mut self, expected: u8) -> bool {
        if self.is_at_end() || (self.source.as_bytes()[self.current] != expected) {
            false
        } else {
            self.current += 1;
            true
        }
    }

    fn string(&mut self) -> Result<Token> {
        while !self.is_at_end() && self.peek() != b'"' {
            if self.peek() == b'\n' {
                self.line += 1;
            }
            self.advance();
        }

        if self.is_at_end() {
            return self.error("Unterminated string.");
        }

        // The closing quote.
        self.advance();
        return self.make_token(TokenType::String);
    }

    fn number(&mut self) -> Result<Token> {
        while Self::is_digit(self.peek()) {
            self.advance();
        }

        // Look for a fractional part.
        if self.peek() == b'.' && Self::is_digit(self.peek_next()) {
            // Consume the "."
            self.advance();

            while Self::is_digit(self.peek()) {
                self.advance();
            }
        }

        self.make_token(TokenType::Number)
    }

    fn identifier(&mut self) -> Result<Token> {
        while Self::is_alpha(self.peek()) || Self::is_digit(self.peek()) {
            self.advance();
        }

        self.make_token(self.identifier_type())
    }

    fn is_digit(c: u8) -> bool {
        c >= b'0' && c <= b'9'
    }

    fn is_alpha(c: u8) -> bool {
        (c >= b'a' && c <= b'z') || (c >= b'A' && c <= b'Z') || c == b'_'
    }

    fn identifier_type(&self) -> TokenType {
        match self.source.as_bytes()[self.start] {
            b'a' => self.check_keyword(1, 2, "nd", TokenType::And),
            b'c' => self.check_keyword(1, 4, "lass", TokenType::Class),
            b'e' => self.check_keyword(1, 3, "lse", TokenType::Else),
            b'f' => {
                if self.current - self.start > 1 {
                    match self.source.as_bytes()[self.start + 1] {
                        b'a' => self.check_keyword(2, 3, "lse", TokenType::False),
                        b'o' => self.check_keyword(2, 1, "r", TokenType::For),
                        b'u' => self.check_keyword(2, 1, "n", TokenType::Fun),
                        _ => TokenType::Identifier,
                    }
                } else {
                    TokenType::Identifier
                }
            }
            b'i' => self.check_keyword(1, 1, "f", TokenType::If),
            b'n' => self.check_keyword(1, 2, "il", TokenType::Nil),
            b'o' => self.check_keyword(1, 1, "r", TokenType::Or),
            b'p' => self.check_keyword(1, 4, "rint", TokenType::Print),
            b'r' => self.check_keyword(1, 5, "eturn", TokenType::Return),
            b's' => self.check_keyword(1, 4, "uper", TokenType::Super),
            b't' => {
                if self.current - self.start > 1 {
                    match self.source.as_bytes()[self.start + 1] {
                        b'h' => self.check_keyword(2, 2, "is", TokenType::This),
                        b'r' => self.check_keyword(2, 2, "ue", TokenType::True),
                        _ => TokenType::Identifier,
                    }
                } else {
                    TokenType::Identifier
                }
            }
            b'v' => self.check_keyword(1, 2, "ar", TokenType::Var),
            b'w' => self.check_keyword(1, 4, "hile", TokenType::While),
            _ => TokenType::Identifier,
        }
    }

    fn check_keyword(
        &self,
        start: usize,
        length: usize,
        rest: &str,
        token_type: TokenType,
    ) -> TokenType {
        if self.current - self.start == start + length &&
            &self.source[self.start + start..self.start + start + length] == rest
        {
            return token_type;
        }

        TokenType::Identifier
    }
}
