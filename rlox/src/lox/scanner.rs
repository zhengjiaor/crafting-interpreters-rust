use std::collections::HashMap;
use std::fmt::{Display, Formatter};

use anyhow::Result;
use lazy_static::lazy_static;
use thiserror::Error;

#[derive(Debug, Clone, Copy, PartialEq)]
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

    Eof,
}

lazy_static! {
    static ref KEYWORDS: HashMap<&'static str, TokenType> = {
        let mut m = HashMap::new();
        m.insert("and", TokenType::And);
        m.insert("class", TokenType::Class);
        m.insert("else", TokenType::Else);
        m.insert("false", TokenType::False);
        m.insert("for", TokenType::For);
        m.insert("fun", TokenType::Fun);
        m.insert("if", TokenType::If);
        m.insert("nil", TokenType::Nil);
        m.insert("or", TokenType::Or);
        m.insert("print", TokenType::Print);
        m.insert("return", TokenType::Return);
        m.insert("super", TokenType::Super);
        m.insert("this", TokenType::This);
        m.insert("true", TokenType::True);
        m.insert("var", TokenType::Var);
        m.insert("while", TokenType::While);
        m
    };
}

#[derive(Clone, Debug, PartialEq)]
pub enum LiteralValue {
    String(String),
    Number(f64),
    False,
    True,
    Nil,
}

impl Display for LiteralValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            LiteralValue::String(s) => write!(f, "{}", s),
            LiteralValue::Number(n) => write!(f, "{}", n),
            LiteralValue::False => write!(f, "false"),
            LiteralValue::True => write!(f, "true"),
            LiteralValue::Nil => write!(f, "nil"),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    pub token_type: TokenType,
    pub lexeme: String,
    pub literal: Option<LiteralValue>,
    pub line: usize,
    pub index: usize,
}

impl Token {
    pub fn new(
        token_type: TokenType,
        lexeme: String,
        literal: Option<LiteralValue>,
        line: usize,
        index: usize,
    ) -> Token {
        Token { token_type, lexeme, literal, line, index }
    }
}

#[derive(Error, Debug)]
#[error("Scan error: {message} at line {line}")]
struct ScanError {
    message: String,
    line: usize,
}

pub struct Scanner {
    source: String,
    tokens: Vec<Token>,
    start: usize,
    current: usize,
    line: usize,
}

impl Scanner {
    pub fn new(source: String) -> Scanner {
        Scanner { source, tokens: Vec::new(), start: 0, current: 0, line: 1 }
    }

    pub fn scan_tokens(mut self) -> Result<Vec<Token>> {
        while !self.is_at_end() {
            self.start = self.current;
            self.scan_token()?;
        }
        self.tokens.push(Token::new(
            TokenType::Eof,
            "".to_string(),
            None,
            self.line,
            self.tokens.len(),
        ));

        Ok(self.tokens)
    }

    fn is_at_end(&self) -> bool {
        self.current >= self.source.len()
    }

    fn scan_token(&mut self) -> Result<()> {
        let c = self.advance();
        match c {
            '(' => self.add_token(TokenType::LeftParen),
            ')' => self.add_token(TokenType::RightParen),
            '{' => self.add_token(TokenType::LeftBrace),
            '}' => self.add_token(TokenType::RightBrace),
            ',' => self.add_token(TokenType::Comma),
            '.' => self.add_token(TokenType::Dot),
            '-' => self.add_token(TokenType::Minus),
            '+' => self.add_token(TokenType::Plus),
            ';' => self.add_token(TokenType::Semicolon),
            '*' => self.add_token(TokenType::Star),
            '!' => {
                let token_type =
                    if self.match_next('=') { TokenType::BangEqual } else { TokenType::Bang };
                self.add_token(token_type);
            }
            '=' => {
                let token_type =
                    if self.match_next('=') { TokenType::EqualEqual } else { TokenType::Equal };
                self.add_token(token_type);
            }
            '<' => {
                let token_type =
                    if self.match_next('=') { TokenType::LessEqual } else { TokenType::Less };
                self.add_token(token_type);
            }
            '>' => {
                let token_type =
                    if self.match_next('=') { TokenType::GreaterEqual } else { TokenType::Greater };
                self.add_token(token_type);
            }
            '/' => {
                if self.match_next('/') {
                    while self.peek() != '\n' && !self.is_at_end() {
                        self.advance();
                    }
                } else {
                    self.add_token(TokenType::Slash);
                }
            }
            ' ' | '\r' | '\t' => {}
            '\n' => {
                self.line += 1;
            }
            '"' => {
                self.string()?;
            }
            d if d.is_ascii_digit() => {
                self.number()?;
            }
            a if a.is_ascii_alphabetic() || a == '_' => {
                self.identifier();
            }
            _ => {
                return Err(ScanError {
                    message: format!("Unexpected character: {}", c),
                    line: self.line,
                }
                .into());
            }
        };

        Ok(())
    }

    fn match_next(&mut self, expected: char) -> bool {
        if self.is_at_end() {
            return false;
        }

        let next = self.source.chars().nth(self.current).unwrap();
        if next != expected {
            return false;
        }

        self.current += 1;
        true
    }

    fn advance(&mut self) -> char {
        let current = self.current;
        self.current += 1;
        self.source.chars().nth(current).unwrap()
    }

    fn peek(&self) -> char {
        if self.is_at_end() {
            return '\0';
        }
        self.source.chars().nth(self.current).unwrap()
    }

    fn peek_next(&self) -> char {
        if self.current + 1 >= self.source.len() {
            return '\0';
        }
        self.source.chars().nth(self.current + 1).unwrap()
    }

    fn string(&mut self) -> Result<()> {
        while self.peek() != '"' && !self.is_at_end() {
            if self.peek() == '\n' {
                self.line += 1;
            }
            self.advance();
        }

        if self.is_at_end() {
            return Err(
                ScanError { message: "Unterminated String".to_string(), line: self.line }.into()
            );
        }

        // The closing ".
        self.advance();

        // Trim the surrounding quotes.
        let value = self.source[self.start + 1..self.current - 1].to_string();
        self.add_token_literal(TokenType::String, Some(LiteralValue::String(value)));
        Ok(())
    }

    fn number(&mut self) -> Result<()> {
        while self.peek().is_ascii_digit() {
            self.advance();
        }

        if self.peek() == '.' && self.peek_next().is_ascii_digit() {
            // Consume the "."
            self.advance();

            while self.peek().is_ascii_digit() {
                self.advance();
            }
        }

        let number = self.source[self.start..self.current].parse::<f64>()?;
        self.add_token_literal(TokenType::Number, Some(LiteralValue::Number(number)));
        Ok(())
    }

    fn identifier(&mut self) {
        while self.peek().is_ascii_alphanumeric() || self.peek() == '_' {
            self.advance();
        }

        let text = &self.source[self.start..self.current];
        match KEYWORDS.get(text) {
            Some(token_type) => self.add_token(token_type.clone()),
            None => self.add_token(TokenType::Identifier),
        }
    }

    fn add_token(&mut self, token_type: TokenType) {
        self.add_token_literal(token_type, None);
    }

    fn add_token_literal(&mut self, token_type: TokenType, literal: Option<LiteralValue>) {
        let text = self.source[self.start..self.current].to_string();
        self.tokens.push(Token::new(token_type, text, literal, self.line, self.tokens.len()));
    }
}
