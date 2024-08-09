use crate::lox::parser::{Expr, Stmt};
use crate::lox::scanner::{LiteralValue, Token, TokenType};

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};
use std::rc::Rc;
use std::time;

use anyhow::{anyhow, Result};
use thiserror::Error;

use super::parser;

#[derive(Clone, Debug, PartialEq)]
pub enum Object {
    String(String),
    Number(f64),
    Boolean(bool),
    Callable(LoxCallable),
    Nil,
    None,
}

impl Display for Object {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Object::String(s) => write!(f, "{}", s),
            Object::Number(n) => write!(f, "{}", n),
            Object::Boolean(b) => write!(f, "{}", b),
            Object::Callable(callable) => write!(f, "{}", callable),
            Object::Nil => write!(f, "nil"),
            Object::None => write!(f, ""),
        }
    }
}

impl Object {
    pub fn new(literal: LiteralValue) -> Object {
        match literal {
            LiteralValue::String(s) => Object::String(s.clone()),
            LiteralValue::Number(n) => Object::Number(n),
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

#[derive(Clone, Debug, PartialEq)]
pub enum LoxCallable {
    NativeFunction { name: String, arity: usize, function: fn(&Vec<Object>) -> Object },
    LoxFunction { declaration: parser::Function, closure: Rc<RefCell<Environment>> },
}

impl Display for LoxCallable {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            LoxCallable::NativeFunction { .. } => write!(f, "<native fn>"),
            LoxCallable::LoxFunction { declaration, .. } => {
                write!(f, "<fn {}>", declaration.name.lexeme)
            }
        }
    }
}

impl LoxCallable {
    pub fn arity(&self) -> usize {
        match self {
            LoxCallable::NativeFunction { arity, .. } => *arity,
            LoxCallable::LoxFunction { declaration, .. } => declaration.params.len(),
        }
    }

    pub fn call(&self, interpreter: &mut Interpreter, arguments: &Vec<Object>) -> Result<Object> {
        match self {
            LoxCallable::NativeFunction { function, .. } => Ok(function(arguments)),
            LoxCallable::LoxFunction { declaration, closure } => {
                self.call_function(declaration, closure, interpreter, arguments)
            }
        }
    }

    fn call_function(
        &self,
        declaration: &parser::Function,
        closure: &Rc<RefCell<Environment>>,
        interpreter: &mut Interpreter,
        arguments: &Vec<Object>,
    ) -> Result<Object> {
        let environment = Rc::new(RefCell::new(Environment::with_enclosing(Rc::clone(closure))));
        for (param, arg) in declaration.params.iter().zip(arguments) {
            environment.borrow_mut().define(&param.lexeme, arg.clone());
        }

        let result = interpreter.execute_block(&declaration.body, environment);
        match result {
            Ok(_) => Ok(Object::Nil),
            Err(e) => match e.downcast_ref() {
                Some(Return(obj)) => Ok(obj.clone()),
                _ => Err(e),
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Default)]
struct Environment {
    values: HashMap<String, Object>,
    enclosing: Option<Rc<RefCell<Environment>>>,
}

impl Environment {
    fn new() -> Environment {
        Environment { values: HashMap::new(), enclosing: None }
    }

    fn with_enclosing(enclosing: Rc<RefCell<Environment>>) -> Environment {
        Environment { values: HashMap::new(), enclosing: Some(Rc::clone(&enclosing)) }
    }

    fn define(&mut self, name: &str, value: Object) {
        self.values.insert(name.to_string(), value);
    }

    fn assign(&mut self, name: &Token, value: Object) -> Result<()> {
        if self.values.contains_key(name.lexeme.as_str()) {
            self.values.insert(name.lexeme.clone(), value);
            Ok(())
        } else if let Some(enclosing) = &self.enclosing {
            enclosing.borrow_mut().assign(name, value)
        } else {
            Err(anyhow!("Undefined variable '{}'.", name.lexeme))
        }
    }

    fn get(&self, name: &Token) -> Result<Object> {
        if self.values.contains_key(name.lexeme.as_str()) {
            Ok(self.values.get(name.lexeme.as_str()).unwrap().clone())
        } else if let Some(enclosing) = &self.enclosing {
            enclosing.as_ref().borrow().get(name)
        } else {
            Err(anyhow!("Undefined variable '{}'.", name.lexeme))
        }
    }
}

#[derive(Clone, Debug, PartialEq, Error)]
#[error("Return: {0}")]
struct Return(Object);

unsafe impl Send for Return {}
unsafe impl Sync for Return {}

pub struct Interpreter {
    globals: Rc<RefCell<Environment>>,
    environment: Rc<RefCell<Environment>>,
}

impl<'a> Interpreter {
    pub fn new() -> Interpreter {
        let globals = Rc::new(RefCell::new(Environment::new()));
        globals.borrow_mut().define(
            "clock",
            Object::Callable(LoxCallable::NativeFunction {
                name: "clock".to_string(),
                arity: 0,
                function: |_| Object::Number(time::Instant::now().elapsed().as_secs_f64()),
            }),
        );
        Interpreter { globals: Rc::clone(&globals), environment: Rc::clone(&globals) }
    }

    pub fn interprete(&mut self, statements: Vec<Stmt>) -> Result<()> {
        for statement in &statements {
            self.execute(statement)?;
        }
        Ok(())
    }

    fn execute(&mut self, statement: &Stmt) -> Result<()> {
        match statement {
            Stmt::If { condition, then_branch, else_branch } => {
                self.visit_if_stmt(condition, then_branch, else_branch)
            }
            Stmt::While { condition, body } => self.visit_while_stmt(condition, body),
            Stmt::Block(statements) => self.visit_block_stmt(statements),
            Stmt::Expression(expr) => self.visit_expression_stmt(expr),
            Stmt::Print(expr) => self.visit_print_stmt(expr),
            Stmt::Var { name, initializer } => self.visit_var_stmt(name, initializer),
            Stmt::Function(func) => self.visit_funtion_stmt(func),
            Stmt::Return { keyword, value } => self.visit_return_stmt(keyword, value),
        }
    }

    fn visit_if_stmt(
        &mut self,
        condition: &Expr,
        then_branch: &Box<Stmt>,
        else_branch: &Option<Box<Stmt>>,
    ) -> Result<()> {
        let condition = self.evaluate(condition)?;
        if condition.is_truthy() {
            self.execute(then_branch)
        } else if let Some(else_branch) = else_branch {
            self.execute(else_branch)
        } else {
            Ok(())
        }
    }

    fn visit_while_stmt(&mut self, condition: &Expr, body: &Box<Stmt>) -> Result<()> {
        while self.evaluate(condition)?.is_truthy() {
            self.execute(body)?;
        }
        Ok(())
    }

    fn visit_block_stmt(&mut self, statements: &Vec<Stmt>) -> Result<()> {
        let environment =
            Rc::new(RefCell::new(Environment::with_enclosing(Rc::clone(&self.environment))));
        self.execute_block(statements, environment)
    }

    fn execute_block(
        &mut self,
        statements: &Vec<Stmt>,
        environment: Rc<RefCell<Environment>>,
    ) -> Result<()> {
        let previous = Rc::clone(&self.environment);
        self.environment = environment;
        for statement in statements {
            self.execute(statement).or_else(|e| {
                self.environment = Rc::clone(&previous);
                Err(e)
            })?;
        }
        self.environment = previous;
        Ok(())
    }

    fn visit_expression_stmt(&mut self, expresson: &Expr) -> Result<()> {
        self.evaluate(expresson)?;
        Ok(())
    }

    fn visit_print_stmt(&mut self, expresson: &Expr) -> Result<()> {
        let obj = self.evaluate(expresson)?;
        Ok(println!("{}", obj))
    }

    fn visit_var_stmt(&mut self, name: &Token, initializer: &Option<Expr>) -> Result<()> {
        let value = match initializer {
            Some(expr) => self.evaluate(expr)?,
            None => Object::Nil,
        };
        Ok(self.environment.borrow_mut().define(&name.lexeme, value))
    }

    fn visit_funtion_stmt(&mut self, func: &parser::Function) -> Result<()> {
        let callable = LoxCallable::LoxFunction {
            declaration: func.clone(),
            closure: Rc::clone(&self.environment),
        };
        self.environment.borrow_mut().define(&func.name.lexeme, Object::Callable(callable));
        Ok(())
    }

    fn visit_return_stmt(&mut self, _: &Token, value: &Option<Expr>) -> Result<()> {
        let result = match value {
            Some(expr) => self.evaluate(expr)?,
            None => Object::Nil,
        };
        Err(Return(result).into())
    }

    fn evaluate(&mut self, expr: &Expr) -> Result<Object> {
        let obj = match expr {
            Expr::Assign { name, value } => self.visit_assign_expr(name, value)?,
            Expr::Literal(literal) => self.visit_literal_expr(literal)?,
            Expr::Call { callee, paren, arguments } => {
                self.visit_call_expr(callee, paren, arguments)?
            }
            Expr::Grouping(inner_expr) => self.visit_grouping_expr(inner_expr)?,
            Expr::Logical { left, op, right } => self.visit_logical_expr(left, op, right)?,
            Expr::Unary { op, right } => self.visit_unary_expr(op, right)?,
            Expr::Binary { left, op, right } => self.visit_binary_expr(left, op, right)?,
            Expr::Variable(token) => self.visit_var_expr(token)?,
        };

        Ok(obj)
    }

    fn visit_assign_expr(&mut self, name: &Token, value: &Expr) -> Result<Object> {
        let value = self.evaluate(value)?;
        self.environment.borrow_mut().assign(&name, value.clone())?;
        Ok(value)
    }

    fn visit_literal_expr(&self, literal: &LiteralValue) -> Result<Object> {
        Ok(Object::new(literal.clone()))
    }

    fn visit_call_expr(
        &mut self,
        callee: &Expr,
        paren: &Token,
        arguments: &Vec<Expr>,
    ) -> Result<Object> {
        let callee = self.evaluate(callee)?;
        if let Object::Callable(callee) = callee {
            let mut args = Vec::new();
            for arg in arguments {
                args.push(self.evaluate(arg)?);
            }

            if args.len() != callee.arity() {
                return Err(anyhow!(
                    "Expected {} arguments but got {}.",
                    callee.arity(),
                    args.len()
                ));
            }

            callee.call(self, &args)
        } else {
            Err(anyhow!("Line {}: Can only call functions and classes: {}", paren.line, callee))
        }
    }

    fn visit_grouping_expr(&mut self, expr: &Expr) -> Result<Object> {
        Ok(self.evaluate(expr)?)
    }

    fn visit_logical_expr(&mut self, left: &Expr, op: &Token, right: &Expr) -> Result<Object> {
        let left = self.evaluate(left)?;
        match op.token_type {
            TokenType::Or => {
                if left.is_truthy() {
                    return Ok(left);
                }
            }
            TokenType::And => {
                if !left.is_truthy() {
                    return Ok(left);
                }
            }
            _ => {
                return Err(anyhow!("visit_logical_expr: unknown logical operator: {}", op.lexeme))
            }
        }

        Ok(self.evaluate(right)?)
    }

    fn visit_unary_expr(&mut self, op: &Token, right: &Expr) -> Result<Object> {
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

    fn visit_binary_expr(&mut self, left: &Expr, op: &Token, right: &Expr) -> Result<Object> {
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

    fn visit_var_expr(&self, name: &Token) -> Result<Object> {
        RefCell::borrow(self.environment.as_ref()).get(name).map(|obj| obj.clone())
    }
}
