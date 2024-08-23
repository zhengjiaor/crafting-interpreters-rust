use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};
use std::rc::Rc;
use std::time;

use anyhow::{anyhow, Result};
use thiserror::Error;

use crate::lox::parser;
use crate::lox::parser::{Expr, Stmt};
use crate::lox::scanner::{LiteralValue, Token, TokenType};

#[derive(Clone, Debug)]
enum Object {
    String(String),
    Number(f64),
    Boolean(bool),
    Callable(LoxCallable),
    Instance(Rc<RefCell<LoxInstance>>),
    Nil,
}

impl PartialEq for Object {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Object::String(s1), Object::String(s2)) => s1 == s2,
            (Object::Number(n1), Object::Number(n2)) => n1 == n2,
            (Object::Boolean(b1), Object::Boolean(b2)) => b1 == b2,
            (Object::Callable(c1), Object::Callable(c2)) => c1 == c2,
            (Object::Instance(i1), Object::Instance(i2)) => Rc::ptr_eq(i1, i2),
            (Object::Nil, Object::Nil) => true,
            _ => false,
        }
    }
}

impl Display for Object {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Object::String(s) => write!(f, "{}", s),
            Object::Number(n) => write!(f, "{}", n),
            Object::Boolean(b) => write!(f, "{}", b),
            Object::Callable(callable) => write!(f, "{}", callable),
            Object::Instance(instance) => write!(f, "{}", instance.borrow()),
            Object::Nil => write!(f, "nil"),
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

trait Call {
    fn arity(&self) -> usize;
    fn call(&self, interpreter: &mut Interpreter, arguments: &Vec<Object>) -> Result<Object>;
}

#[derive(Clone, Debug, PartialEq)]
struct NativeFunction {
    name: String,
    arity: usize,
    function: fn(&Vec<Object>) -> Object,
}

impl Display for NativeFunction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "<native fn>")
    }
}

impl Call for NativeFunction {
    fn arity(&self) -> usize {
        self.arity
    }

    fn call(&self, _interpreter: &mut Interpreter, arguments: &Vec<Object>) -> Result<Object> {
        Ok((self.function)(arguments))
    }
}

impl NativeFunction {
    pub fn new(name: String, arity: usize, function: fn(&Vec<Object>) -> Object) -> NativeFunction {
        NativeFunction { name, arity, function }
    }
}

#[derive(Clone, Debug)]
struct LoxFunction {
    declaration: parser::Function,
    closure: Rc<RefCell<Environment>>,
    is_initializer: bool,
}

impl PartialEq for LoxFunction {
    fn eq(&self, other: &Self) -> bool {
        self.declaration == other.declaration &&
            self.is_initializer == other.is_initializer &&
            Rc::ptr_eq(&self.closure, &other.closure)
    }
}

impl Display for LoxFunction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "<fn {}>", self.declaration.name.lexeme)
    }
}

impl Call for LoxFunction {
    fn arity(&self) -> usize {
        self.declaration.params.len()
    }

    fn call(&self, interpreter: &mut Interpreter, arguments: &Vec<Object>) -> Result<Object> {
        let environment =
            Rc::new(RefCell::new(Environment::with_enclosing(Rc::clone(&self.closure))));
        for (param, arg) in self.declaration.params.iter().zip(arguments) {
            RefCell::borrow_mut(&environment).define(&param.lexeme, arg.clone());
        }

        let result = interpreter.execute_block(&self.declaration.body, environment);
        match result {
            Ok(_) => {
                if self.is_initializer {
                    Ok(RefCell::borrow(&self.closure).get_at(0, "this")?)
                } else {
                    Ok(Object::Nil)
                }
            }
            Err(e) => match e.downcast_ref() {
                Some(Return(obj)) => {
                    if self.is_initializer {
                        Ok(RefCell::borrow(&self.closure).get_at(0, "this")?)
                    } else {
                        Ok(obj.clone())
                    }
                }
                _ => Err(e),
            },
        }
    }
}

impl LoxFunction {
    pub fn new(
        declaration: parser::Function,
        closure: Rc<RefCell<Environment>>,
        is_initializer: bool,
    ) -> LoxFunction {
        LoxFunction { declaration, closure, is_initializer }
    }

    pub fn bind(&self, instance: &Rc<RefCell<LoxInstance>>) -> LoxFunction {
        let environment =
            Rc::new(RefCell::new(Environment::with_enclosing(Rc::clone(&self.closure))));
        RefCell::borrow_mut(&environment).define("this", Object::Instance(Rc::clone(instance)));
        LoxFunction::new(self.declaration.clone(), environment, self.is_initializer)
    }
}

#[derive(Clone, Debug, PartialEq)]
struct LoxClass {
    name: String,
    superclass: Option<Rc<LoxClass>>,
    methods: HashMap<String, LoxCallable>,
}

impl Display for LoxClass {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl Call for Rc<LoxClass> {
    fn arity(&self) -> usize {
        if let Some(LoxCallable::LoxFunction(initializer)) = self.find_method("init") {
            initializer.declaration.params.len()
        } else {
            0
        }
    }

    fn call(&self, interpreter: &mut Interpreter, arguments: &Vec<Object>) -> Result<Object> {
        let instance = Rc::new(RefCell::new(LoxInstance::new(self.clone())));
        if let Some(LoxCallable::LoxFunction(initializer)) = self.find_method("init") {
            initializer.bind(&instance).call(interpreter, arguments)?;
        }
        Ok(Object::Instance(instance))
    }
}

impl LoxClass {
    pub fn find_method(&self, name: &str) -> Option<&LoxCallable> {
        let method = self.methods.get(name);
        if method.is_some() {
            return method;
        }

        if let Some(superclass) = &self.superclass {
            superclass.find_method(name)
        } else {
            None
        }
    }
}

#[derive(Clone, Debug)]
pub enum LoxCallable {
    NativeFunction(NativeFunction),
    LoxFunction(LoxFunction),
    LoxClass(Rc<LoxClass>),
}

impl PartialEq for LoxCallable {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (LoxCallable::NativeFunction(n1), LoxCallable::NativeFunction(n2)) => n1 == n2,
            (LoxCallable::LoxFunction(l1), LoxCallable::LoxFunction(l2)) => l1 == l2,
            (LoxCallable::LoxClass(c1), LoxCallable::LoxClass(c2)) => Rc::ptr_eq(c1, c2),
            _ => false,
        }
    }
}

impl Display for LoxCallable {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            LoxCallable::NativeFunction(func) => write!(f, "{}", func),
            LoxCallable::LoxFunction(func) => write!(f, "{}", func),
            LoxCallable::LoxClass(klass) => write!(f, "{}", klass.as_ref()),
        }
    }
}

impl LoxCallable {
    pub fn arity(&self) -> usize {
        match self {
            LoxCallable::NativeFunction(func) => func.arity(),
            LoxCallable::LoxFunction(func) => func.arity(),
            LoxCallable::LoxClass(klass) => klass.arity(),
        }
    }

    fn call(&self, interpreter: &mut Interpreter, arguments: &Vec<Object>) -> Result<Object> {
        match self {
            LoxCallable::NativeFunction(func) => Ok((func.function)(arguments)),
            LoxCallable::LoxFunction(func) => func.call(interpreter, arguments),
            LoxCallable::LoxClass(klass) => klass.call(interpreter, arguments),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
struct LoxInstance {
    klass: Rc<LoxClass>,
    fields: HashMap<String, Object>,
}

impl Display for LoxInstance {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} instance", self.klass.name)
    }
}

impl LoxInstance {
    pub fn new(klass: Rc<LoxClass>) -> LoxInstance {
        LoxInstance { klass, fields: HashMap::new() }
    }

    pub fn get(&self, me: &Rc<RefCell<Self>>, name: &Token) -> Result<Object> {
        if let Some(field) = self.fields.get(&name.lexeme) {
            Ok(field.clone())
        } else if let Some(LoxCallable::LoxFunction(method)) = self.klass.find_method(&name.lexeme)
        {
            Ok(Object::Callable(LoxCallable::LoxFunction(method.bind(&Rc::clone(me)))))
        } else {
            Err(error(name, format!("Undefined property '{}'.", name.lexeme).as_str()))
        }
    }

    pub fn set(&mut self, name: &Token, value: Object) {
        self.fields.insert(name.lexeme.clone(), value);
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
            RefCell::borrow_mut(&enclosing).assign(name, value)
        } else {
            Err(error(name, format!("Undefined variable '{}'.", name.lexeme).as_str()))
        }
    }

    fn get(&self, name: &Token) -> Result<Object> {
        if self.values.contains_key(name.lexeme.as_str()) {
            Ok(self.values.get(name.lexeme.as_str()).unwrap().clone())
        } else if let Some(enclosing) = &self.enclosing {
            enclosing.as_ref().borrow().get(name)
        } else {
            Err(error(name, format!("Undefined variable '{}'.", name.lexeme).as_str()))
        }
    }

    fn get_at(&self, distance: usize, name: &str) -> Result<Object> {
        if distance == 0 {
            return self
                .values
                .get(name)
                .map(|v| v.clone())
                .ok_or_else(|| anyhow::anyhow!("Undefined variable '{}'.", name));
        }
        self.ancestor(distance)
            .borrow()
            .values
            .get(name)
            .map(|v| v.clone())
            .ok_or_else(|| anyhow::anyhow!("Undefined variable '{}'.", name))
    }

    fn assign_at(&mut self, distance: usize, name: &Token, value: Object) -> Result<()> {
        if distance == 0 {
            if self.values.contains_key(name.lexeme.as_str()) {
                self.values.insert(name.lexeme.clone(), value);
                Ok(())
            } else {
                Err(error(name, format!("Undefined variable '{}'.", name.lexeme).as_str()))
            }
        } else {
            let anc = self.ancestor(distance);
            if anc.borrow().values.contains_key(name.lexeme.as_str()) {
                RefCell::borrow_mut(&anc).values.insert(name.lexeme.clone(), value);
                Ok(())
            } else {
                Err(error(name, format!("Undefined variable '{}'.", name.lexeme).as_str()))
            }
        }
    }

    fn ancestor(&self, distance: usize) -> Rc<RefCell<Environment>> {
        let mut environment = Rc::clone(&self.enclosing.as_ref().unwrap());
        for _ in 1..distance {
            let enclosing = Rc::clone(&environment.borrow().enclosing.as_ref().unwrap());
            environment = enclosing;
        }
        environment
    }
}

#[derive(Clone, Debug, PartialEq, Error)]
#[error("Return: {0}")]
struct Return(Object);

unsafe impl Send for Return {}
unsafe impl Sync for Return {}

fn error(token: &Token, message: &str) -> anyhow::Error {
    anyhow!("{}\n[line {}]", message, token.line)
}

pub struct Interpreter {
    globals: Rc<RefCell<Environment>>,
    environment: Rc<RefCell<Environment>>,
    locals: HashMap<usize, usize>,
}

impl Interpreter {
    pub fn new() -> Interpreter {
        let globals = Rc::new(RefCell::new(Environment::new()));
        RefCell::borrow_mut(&globals).define(
            "clock",
            Object::Callable(LoxCallable::NativeFunction(NativeFunction::new(
                "clock".to_string(),
                0,
                |_| {
                    Object::Number(
                        time::SystemTime::now()
                            .duration_since(time::SystemTime::UNIX_EPOCH)
                            .map(|d| d.as_secs_f64())
                            .unwrap_or(0.0),
                    )
                },
            ))),
        );
        Interpreter {
            globals: Rc::clone(&globals),
            environment: Rc::clone(&globals),
            locals: HashMap::new(),
        }
    }

    pub fn interpret(&mut self, statements: Vec<Stmt>) -> Result<()> {
        for statement in &statements {
            if let Err(error) = self.execute(statement) {
                eprintln!("{}", error);
                return Err(anyhow!("Runtime error"));
            }
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
            Stmt::Class { name, superclass, methods } => {
                self.visit_class_stmt(name, superclass, methods)
            }
        }
    }

    pub fn resolve(&mut self, name: &Token, depth: usize) {
        self.locals.insert(name.index, depth);
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
        Ok(RefCell::borrow_mut(&self.environment).define(&name.lexeme, value))
    }

    fn visit_funtion_stmt(&mut self, func: &parser::Function) -> Result<()> {
        let callable = LoxCallable::LoxFunction(LoxFunction::new(
            func.clone(),
            Rc::clone(&self.environment),
            false,
        ));
        RefCell::borrow_mut(&self.environment)
            .define(&func.name.lexeme, Object::Callable(callable));
        Ok(())
    }

    fn visit_return_stmt(&mut self, _: &Token, value: &Option<Expr>) -> Result<()> {
        let result = match value {
            Some(expr) => self.evaluate(expr)?,
            None => Object::Nil,
        };
        Err(Return(result).into())
    }

    fn visit_class_stmt(
        &mut self,
        name: &Token,
        superclass: &Option<Expr>,
        methods: &Vec<parser::Function>,
    ) -> Result<()> {
        let mut my_super = None;
        if let Some(superclass) = superclass {
            if let Object::Callable(LoxCallable::LoxClass(superclass)) =
                self.evaluate(superclass)?
            {
                my_super = Some(superclass);
            } else {
                return Err(error(name, "Superclass must be a class."));
            }
        }

        RefCell::borrow_mut(&self.environment).define(&name.lexeme, Object::Nil);

        let environment = Rc::clone(&self.environment);
        let has_super = my_super.is_some();
        if has_super {
            self.environment =
                Rc::new(RefCell::new(Environment::with_enclosing(Rc::clone(&self.environment))));
            RefCell::borrow_mut(&self.environment).define(
                "super",
                Object::Callable(LoxCallable::LoxClass(Rc::clone(my_super.as_ref().unwrap()))),
            );
        }

        let mut method_map = HashMap::new();
        for method in methods {
            let callable = LoxCallable::LoxFunction(LoxFunction::new(
                method.clone(),
                Rc::clone(&self.environment),
                method.name.lexeme == "init",
            ));
            method_map.insert(method.name.lexeme.clone(), callable);
        }

        let klass = LoxCallable::LoxClass(Rc::new(LoxClass {
            name: name.lexeme.clone(),
            superclass: my_super,
            methods: method_map,
        }));

        if has_super {
            self.environment = environment;
        }
        RefCell::borrow_mut(&self.environment).assign(&name, Object::Callable(klass))?;
        Ok(())
    }

    fn evaluate(&mut self, expr: &Expr) -> Result<Object> {
        match expr {
            Expr::Assign { name, value } => self.visit_assign_expr(name, value),
            Expr::Literal(literal) => self.visit_literal_expr(literal),
            Expr::Call { callee, paren, arguments } => {
                self.visit_call_expr(callee, paren, arguments)
            }
            Expr::Get { expr, name } => self.visit_get_expr(expr, name),
            Expr::Grouping(inner_expr) => self.visit_grouping_expr(inner_expr),
            Expr::Logical { left, op, right } => self.visit_logical_expr(left, op, right),
            Expr::Set { ojbect, name, value } => self.visit_set_expr(ojbect, name, value),
            Expr::Super { keyword, method } => self.visit_super_expr(keyword, method),
            Expr::Unary { op, right } => self.visit_unary_expr(op, right),
            Expr::Binary { left, op, right } => self.visit_binary_expr(left, op, right),
            Expr::Variable(token) => self.visit_var_expr(token),
            Expr::This(keyword) => self.visit_this_expr(keyword),
        }
    }

    fn visit_assign_expr(&mut self, name: &Token, value: &Expr) -> Result<Object> {
        let value = self.evaluate(value)?;
        if let Some(distance) = self.locals.get(&name.index) {
            RefCell::borrow_mut(&self.environment).assign_at(*distance, name, value.clone())?;
        } else {
            RefCell::borrow_mut(&self.globals).assign(name, value.clone())?;
        }

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
                return Err(error(
                    paren,
                    &format!("Expected {} arguments but got {}.", callee.arity(), args.len()),
                ));
            }

            callee.call(self, &args)
        } else {
            Err(error(paren, "Can only call functions and classes."))
        }
    }

    fn visit_get_expr(&mut self, expr: &Expr, name: &Token) -> Result<Object> {
        if let Object::Instance(instance) = self.evaluate(expr)? {
            return instance.borrow().get(&instance, name);
        }
        Err(error(name, "Only instances have properties."))
    }

    fn visit_set_expr(&mut self, object: &Expr, name: &Token, value: &Expr) -> Result<Object> {
        if let Object::Instance(instance) = self.evaluate(object)? {
            let value = self.evaluate(value)?;
            RefCell::borrow_mut(&instance).set(&name, value.clone());
            return Ok(value);
        }
        Err(error(name, "Only instances have fields."))
    }

    fn visit_super_expr(&mut self, keyword: &Token, method: &Token) -> Result<Object> {
        if let Some(distance) = self.locals.get(&keyword.index) {
            let superclass = RefCell::borrow(&self.environment).get_at(*distance, "super")?;
            let instance = RefCell::borrow(&self.environment).get_at(*distance - 1, "this")?;

            if let Object::Instance(instance) = instance {
                if let Object::Callable(LoxCallable::LoxClass(klass)) = superclass {
                    if let Some(LoxCallable::LoxFunction(method)) =
                        klass.find_method(&method.lexeme)
                    {
                        return Ok(Object::Callable(LoxCallable::LoxFunction(
                            method.bind(&instance),
                        )));
                    }
                }
            }
        }

        Err(error(method, format!("Undefined property '{}'.", method.lexeme).as_str()))
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
                return Err(error(op, "visit_logical_expr: unknown logical operator"));
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
                    Err(error(op, "Operand must be a number."))
                }
            }
            TokenType::Bang => Ok(Object::Boolean(!right.is_truthy())),
            _ => Err(error(op, "visit_unary_expr: unknown unary operator")),
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
                    Err(error(op, "Operands must be numbers."))
                }
            }
            TokenType::Slash => {
                if let (Object::Number(left), Object::Number(right)) = (&left, &right) {
                    Ok(Object::Number(left / right))
                } else {
                    Err(error(op, "Operands must be numbers."))
                }
            }
            TokenType::Star => {
                if let (Object::Number(left), Object::Number(right)) = (&left, &right) {
                    Ok(Object::Number(left * right))
                } else {
                    Err(error(op, "Operands must be numbers."))
                }
            }
            TokenType::Plus => {
                if let (Object::Number(left), Object::Number(right)) = (&left, &right) {
                    Ok(Object::Number(left + right))
                } else if let (Object::String(left), Object::String(right)) = (&left, &right) {
                    Ok(Object::String(format!("{}{}", left, right)))
                } else {
                    Err(error(op, "Operands must be two numbers or two strings."))
                }
            }
            TokenType::Greater => {
                if let (Object::Number(left), Object::Number(right)) = (&left, &right) {
                    Ok(Object::Boolean(left > right))
                } else {
                    Err(error(op, "Operands must be numbers."))
                }
            }
            TokenType::GreaterEqual => {
                if let (Object::Number(left), Object::Number(right)) = (&left, &right) {
                    Ok(Object::Boolean(left >= right))
                } else {
                    Err(error(op, "Operands must be numbers."))
                }
            }
            TokenType::Less => {
                if let (Object::Number(left), Object::Number(right)) = (&left, &right) {
                    Ok(Object::Boolean(left < right))
                } else {
                    Err(error(op, "Operands must be numbers."))
                }
            }
            TokenType::LessEqual => {
                if let (Object::Number(left), Object::Number(right)) = (&left, &right) {
                    Ok(Object::Boolean(left <= right))
                } else {
                    Err(error(op, "Operands must be numbers."))
                }
            }
            TokenType::BangEqual => Ok(Object::Boolean(left != right)),
            TokenType::EqualEqual => Ok(Object::Boolean(left == right)),
            _ => Err(error(op, "visit_binary_expr: unknown binary operator")),
        }
    }

    fn visit_var_expr(&self, name: &Token) -> Result<Object> {
        self.lookup_variable(name)
    }

    fn visit_this_expr(&self, keyword: &Token) -> Result<Object> {
        self.lookup_variable(keyword)
    }

    fn lookup_variable(&self, name: &Token) -> Result<Object> {
        if let Some(distance) = self.locals.get(&name.index) {
            self.environment.borrow().get_at(*distance, &name.lexeme)
        } else {
            self.globals.borrow().get(name)
        }
    }
}
