use crate::lox::parser::Expr;
use crate::lox::scanner::{LiteralValue, Token, TokenType};

use std::fmt::{Display, Formatter};

use anyhow::{anyhow, Result};

#[derive(Clone, Debug, PartialEq)]
pub enum Object {
    String(String),
    Number(f64),
    Boolean(bool),
    Nil,
    None,
}

impl Display for Object {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Object::String(s) => write!(f, "{}", s),
            Object::Number(n) => write!(f, "{}", n),
            Object::Boolean(b) => write!(f, "{}", b),
            Object::Nil => write!(f, "nil"),
            Object::None => write!(f, ""),
        }
    }
}

impl Object {
    pub fn new(literal: &LiteralValue) -> Object {
        match literal {
            LiteralValue::String(s) => Object::String(s.clone()),
            LiteralValue::Number(n) => Object::Number(*n),
            LiteralValue::False => Object::Boolean(false),
            LiteralValue::True => Object::Boolean(true),
            LiteralValue::Nil => Object::Nil,
            LiteralValue::None => Object::None,
        }
    }

    fn is_truthy(&self) -> bool {
        match self {
            Object::Nil => false,
            Object::Boolean(b) => *b,
            _ => true,
        }
    }
}

pub struct Interpreter {}

impl Interpreter {
    pub fn new() -> Interpreter {
        Interpreter {}
    }

    pub fn evaluate(&self, expr: &Expr) -> Result<Object> {
        let obj = match expr {
            Expr::Literal(literal) => self.visit_literal_expr(literal)?,
            Expr::Grouping(inner_expr) => self.visit_grouping_expr(inner_expr)?,
            Expr::Unary { op, right } => self.visit_unary_expr(op, right)?,
            Expr::Binary { left, op, right } => self.visit_binary_expr(left, op, right)?,
        };

        Ok(obj)
    }

    fn visit_literal_expr(&self, literal: &LiteralValue) -> Result<Object> {
        Ok(Object::new(literal))
    }

    fn visit_grouping_expr(&self, expr: &Expr) -> Result<Object> {
        Ok(self.evaluate(expr)?)
    }

    fn visit_unary_expr(&self, op: &Token, right: &Expr) -> Result<Object> {
        let right = self.evaluate(right)?;
        match op.token_type {
            TokenType::Minus => {
                if let Object::Number(num) = right {
                    Ok(Object::Number(-num))
                } else {
                    Err(anyhow!("visit_unary_expr: right is not a Number: {}", right))
                }
            }
            TokenType::Bang => Ok(Object::Boolean(!right.is_truthy())),
            _ => Err(anyhow!("visit_unary_expr: unknown unary operator: {}", op.lexeme)),
        }
    }

    fn visit_binary_expr(&self, left: &Expr, op: &Token, right: &Expr) -> Result<Object> {
        let left = self.evaluate(left)?;
        let right = self.evaluate(right)?;

        match op.token_type {
            TokenType::Minus => {
                if let (Object::Number(left), Object::Number(right)) = (&left, &right) {
                    Ok(Object::Number(left - right))
                } else {
                    Err(anyhow!(
                        "visit_binary_expr: left or right is not a Number: {} - {}",
                        left,
                        right
                    ))
                }
            }
            TokenType::Slash => {
                if let (Object::Number(left), Object::Number(right)) = (&left, &right) {
                    Ok(Object::Number(left / right))
                } else {
                    Err(anyhow!(
                        "visit_binary_expr: left or right is not a Number: {} / {}",
                        left,
                        right
                    ))
                }
            }
            TokenType::Star => {
                if let (Object::Number(left), Object::Number(right)) = (&left, &right) {
                    Ok(Object::Number(left * right))
                } else {
                    Err(anyhow!(
                        "visit_binary_expr: left or right is not a Number: {} * {}",
                        left,
                        right
                    ))
                }
            }
            TokenType::Plus => {
                if let (Object::Number(left), Object::Number(right)) = (&left, &right) {
                    Ok(Object::Number(left + right))
                } else if let (Object::String(left), Object::String(right)) = (&left, &right) {
                    Ok(Object::String(format!("{}{}", left, right)))
                } else {
                    Err(anyhow!(
                        "visit_binary_expr: left or right is not a Number or String: {} + {}",
                        left,
                        right
                    ))
                }
            }
            TokenType::Greater => {
                if let (Object::Number(left), Object::Number(right)) = (&left, &right) {
                    Ok(Object::Boolean(left > right))
                } else {
                    Err(anyhow!(
                        "visit_binary_expr: left or right is not a Number: {} > {}",
                        left,
                        right
                    ))
                }
            }
            TokenType::GreaterEqual => {
                if let (Object::Number(left), Object::Number(right)) = (&left, &right) {
                    Ok(Object::Boolean(left >= right))
                } else {
                    Err(anyhow!(
                        "visit_binary_expr: left or right is not a Number: {} >= {}",
                        left,
                        right
                    ))
                }
            }
            TokenType::Less => {
                if let (Object::Number(left), Object::Number(right)) = (&left, &right) {
                    Ok(Object::Boolean(left < right))
                } else {
                    Err(anyhow!(
                        "visit_binary_expr: left or right is not a Number: {} < {}",
                        left,
                        right
                    ))
                }
            }
            TokenType::LessEqual => {
                if let (Object::Number(left), Object::Number(right)) = (&left, &right) {
                    Ok(Object::Boolean(left <= right))
                } else {
                    Err(anyhow!(
                        "visit_binary_expr: left or right is not a Number: {} <= {}",
                        left,
                        right
                    ))
                }
            }
            TokenType::BangEqual => Ok(Object::Boolean(left != right)),
            TokenType::EqualEqual => Ok(Object::Boolean(left == right)),
            _ => Err(anyhow!("visit_binary_expr: unknown binary operator: {}", op.lexeme)),
        }
    }
}
