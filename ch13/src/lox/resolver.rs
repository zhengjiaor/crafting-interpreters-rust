use std::collections::HashMap;

use crate::lox::scanner::{LiteralValue, Token, TokenType};
use crate::lox::{
    interpreter::Interpreter,
    parser,
    parser::{Expr, Stmt},
};

use anyhow::{anyhow, Result};

use super::interpreter::Object;

#[derive(Clone, Copy, PartialEq, Eq)]
enum FunctionType {
    None,
    Function,
    Initializer,
    Method,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ClassType {
    None,
    Class,
    SubClass,
}

pub struct Resolver<'a> {
    interpreter: &'a mut Interpreter,
    scopes: Vec<HashMap<String, bool>>,
    current_function: FunctionType,
    current_class: ClassType,
}

impl<'a> Resolver<'a> {
    pub fn new(interpreter: &'a mut Interpreter) -> Resolver<'a> {
        Resolver {
            interpreter,
            scopes: Vec::new(),
            current_function: FunctionType::None,
            current_class: ClassType::None,
        }
    }

    pub fn resolve_stmts(&mut self, statements: &Vec<Stmt>) -> Result<()> {
        for statement in statements {
            self.resolve_stmt(statement)?;
        }
        Ok(())
    }

    fn resolve_stmt(&mut self, statement: &Stmt) -> Result<()> {
        match statement {
            Stmt::Var { name, initializer } => self.visit_var_stmt(name, initializer),
            Stmt::Function(func) => self.visit_funtion_stmt(func),
            Stmt::Expression(expr) => self.visit_expression_stmt(expr),
            Stmt::If { condition, then_branch, else_branch } => {
                self.visit_if_stmt(condition, then_branch, else_branch)
            }
            Stmt::Print(expr) => self.visit_print_stmt(expr),
            Stmt::Return { keyword, value } => self.visit_return_stmt(keyword, value),
            Stmt::While { condition, body } => self.visit_while_stmt(condition, body),
            Stmt::Block(statements) => self.visit_block_stmt(statements),
            Stmt::Class { name, superclass, methods } => {
                self.visit_class_stmt(name, superclass, methods)
            }
        }
    }

    fn visit_var_stmt(&mut self, name: &Token, initializer: &Option<Expr>) -> Result<()> {
        self.declare(name)?;
        if let Some(initializer) = initializer {
            self.resolve_expr(initializer)?;
        }
        self.define(name);
        Ok(())
    }

    fn visit_funtion_stmt(&mut self, func: &parser::Function) -> Result<()> {
        self.declare(&func.name)?;
        self.define(&func.name);
        self.resolve_function(func, FunctionType::Function)
    }

    fn resolve_function(&mut self, func: &parser::Function, func_type: FunctionType) -> Result<()> {
        let enclosing_function = self.current_function;
        self.current_function = func_type;

        let result = || -> Result<()> {
            self.begin_scope();
            for param in &func.params {
                self.declare(param)?;
                self.define(param);
            }
            self.resolve_stmts(&func.body)?;
            self.end_scope();
            Ok(())
        }();
        self.current_function = enclosing_function;
        result
    }

    fn visit_expression_stmt(&mut self, expr: &Expr) -> Result<()> {
        self.resolve_expr(expr)
    }

    fn visit_if_stmt(
        &mut self,
        condition: &Expr,
        then_branch: &Stmt,
        else_branch: &Option<Box<Stmt>>,
    ) -> Result<()> {
        self.resolve_expr(condition)?;
        self.resolve_stmt(then_branch)?;
        if let Some(else_branch) = else_branch {
            self.resolve_stmt(else_branch)?;
        }
        Ok(())
    }

    fn visit_print_stmt(&mut self, expr: &Expr) -> Result<()> {
        self.resolve_expr(expr)
    }

    fn visit_return_stmt(&mut self, _keyword: &Token, value: &Option<Expr>) -> Result<()> {
        if self.current_function == FunctionType::None {
            return Err(anyhow!("Cannot return from top-level code"));
        }

        if let Some(value) = value {
            if self.current_function == FunctionType::Initializer {
                return Err(anyhow!("Cannot return a value from an initializer"));
            }

            self.resolve_expr(value)?;
        }
        Ok(())
    }

    fn visit_while_stmt(&mut self, condition: &Expr, body: &Stmt) -> Result<()> {
        self.resolve_expr(condition)?;
        self.resolve_stmt(body)
    }

    fn visit_block_stmt(&mut self, statements: &Vec<Stmt>) -> Result<()> {
        self.begin_scope();
        self.resolve_stmts(statements)?;
        self.end_scope();
        Ok(())
    }

    fn visit_class_stmt(
        &mut self,
        name: &Token,
        superclass: &Option<Expr>,
        methods: &Vec<parser::Function>,
    ) -> Result<()> {
        let enclosing_class = self.current_class;
        self.current_class = ClassType::Class;

        self.declare(name)?;
        self.define(name);

        if let Some(superclass) = superclass {
            if let Expr::Variable(super_name) = superclass {
                if super_name.lexeme == name.lexeme {
                    return Err(anyhow!("A class cannot inherit from itself."));
                }
            }

            self.current_class = ClassType::SubClass;
            self.resolve_expr(superclass)?;

            self.begin_scope();
            self.scopes.last_mut().unwrap().insert("super".to_string(), true);
        }

        self.begin_scope();
        self.scopes.last_mut().unwrap().insert("this".to_string(), true);

        for method in methods {
            let func_type = if method.name.lexeme == "init" {
                FunctionType::Initializer
            } else {
                FunctionType::Method
            };
            self.resolve_function(method, func_type)?;
        }

        if superclass.is_some() {
            self.end_scope();
        }

        self.end_scope();

        self.current_class = enclosing_class;
        Ok(())
    }

    fn begin_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn end_scope(&mut self) {
        self.scopes.pop();
    }

    fn declare(&mut self, name: &Token) -> Result<()> {
        if let Some(scope) = self.scopes.last_mut() {
            if scope.contains_key(&name.lexeme) {
                return Err(anyhow!(
                    "Already a variable with this name in this scope: {}",
                    name.lexeme
                ));
            }
            scope.insert(name.lexeme.clone(), false);
        }

        Ok(())
    }

    fn define(&mut self, name: &Token) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name.lexeme.clone(), true);
        }
    }

    fn resolve_expr(&mut self, expr: &Expr) -> Result<()> {
        match expr {
            Expr::Variable(name) => self.visit_var_expr(name),
            Expr::Assign { name, value } => self.visit_assign_expr(name, value),
            Expr::Binary { left, op, right } => self.visit_binary_expr(left, op, right),
            Expr::Call { callee, paren, arguments } => {
                self.visit_call_expr(callee, paren, arguments)
            }
            Expr::Get { expr, name } => self.visit_get_expr(expr, name),
            Expr::Grouping(expr) => self.visit_grouping_expr(expr),
            Expr::Literal(literal) => self.visit_literal_expr(literal),
            Expr::Logical { left, op, right } => self.visit_logical_expr(left, op, right),
            Expr::Set { ojbect, name, value } => self.visit_set_expr(ojbect, name, value),
            Expr::Super { keyword, method } => self.visit_super_expr(keyword, method),
            Expr::This(keyword) => self.visit_this_expr(keyword),
            Expr::Unary { op, right } => self.visit_unary_expr(op, right),
        }
    }

    fn visit_var_expr(&mut self, name: &Token) -> Result<()> {
        if !self.scopes.is_empty() &&
            self.scopes.last().is_some() &&
            self.scopes.last().unwrap().get(&name.lexeme) == Some(&false)
        {
            return Err(anyhow!(
                "Cannot read local variable in its own initializer: {}",
                name.lexeme
            ));
        }

        Ok(self.resolve_local(name))
    }

    fn visit_assign_expr(&mut self, name: &Token, value: &Expr) -> Result<()> {
        self.resolve_expr(value)?;
        Ok(self.resolve_local(name))
    }

    fn visit_binary_expr(&mut self, left: &Expr, _op: &Token, right: &Expr) -> Result<()> {
        self.resolve_expr(left)?;
        self.resolve_expr(right)
    }

    fn visit_call_expr(
        &mut self,
        callee: &Expr,
        _paren: &Token,
        arguments: &Vec<Expr>,
    ) -> Result<()> {
        self.resolve_expr(callee)?;
        for arg in arguments {
            self.resolve_expr(arg)?;
        }
        Ok(())
    }

    fn visit_get_expr(&mut self, expr: &Expr, _name: &Token) -> Result<()> {
        self.resolve_expr(expr)
    }

    fn visit_grouping_expr(&mut self, expr: &Expr) -> Result<()> {
        self.resolve_expr(expr)
    }

    fn visit_literal_expr(&mut self, _: &LiteralValue) -> Result<()> {
        Ok(())
    }

    fn visit_logical_expr(&mut self, left: &Expr, _op: &Token, right: &Expr) -> Result<()> {
        self.resolve_expr(left)?;
        self.resolve_expr(right)
    }

    fn visit_set_expr(&mut self, ojbect: &Expr, _name: &Token, value: &Expr) -> Result<()> {
        self.resolve_expr(value)?;
        self.resolve_expr(ojbect)
    }

    fn visit_super_expr(&mut self, keyword: &Token, _method: &Token) -> Result<()> {
        match self.current_class {
            ClassType::None => Err(anyhow!("Cannot use 'super' outside of a class")),
            ClassType::SubClass => Ok(self.resolve_local(keyword)),
            _ => Err(anyhow!("Can't use 'super' in a class with no superclass.")),
        }
    }

    fn visit_this_expr(&mut self, keyword: &Token) -> Result<()> {
        if self.current_class == ClassType::None {
            return Err(anyhow!("Cannot use 'this' outside of a class"));
        }

        self.resolve_local(keyword);
        Ok(())
    }

    fn visit_unary_expr(&mut self, _op: &Token, right: &Expr) -> Result<()> {
        self.resolve_expr(right)
    }

    fn resolve_local(&mut self, name: &Token) {
        for (i, scope) in self.scopes.iter().enumerate().rev() {
            if scope.contains_key(&name.lexeme) {
                self.interpreter.resolve(name, self.scopes.len() - 1 - i);
            }
        }
    }
}
