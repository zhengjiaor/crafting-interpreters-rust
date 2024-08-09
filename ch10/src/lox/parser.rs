use std::fmt::Display;

use crate::lox::scanner::{Token, TokenType};

use anyhow::{Error, Result};

use super::scanner::LiteralValue;

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Assign { name: Token, value: Box<Expr> },
    Binary { left: Box<Expr>, op: Token, right: Box<Expr> },
    Call { callee: Box<Expr>, paren: Token, arguments: Vec<Expr> },
    Grouping(Box<Expr>),
    Literal(LiteralValue),
    Logical { left: Box<Expr>, op: Token, right: Box<Expr> },
    Unary { op: Token, right: Box<Expr> },
    Variable(Token),
}

pub fn format_ast(expr: &Expr) -> String {
    match expr {
        Expr::Assign { name, value } => {
            let value_str = format_ast(value);
            format!("(= {} {})", name.lexeme, value_str)
        }
        Expr::Binary { left, op, right } => {
            let left_str = format_ast(left);
            let right_str = format_ast(right);
            format!("({} {} {})", op.lexeme, left_str, right_str)
        }
        Expr::Call { callee, paren, arguments } => {
            let callee_str = format_ast(callee);
            let arguments_str =
                arguments.iter().map(|arg| format_ast(arg)).collect::<Vec<_>>().join(" ");
            format!("(call {} {})", callee_str, arguments_str)
        }
        Expr::Grouping(expr) => {
            let expr_str = format_ast(expr);
            format!("(group {})", expr_str)
        }
        Expr::Literal(literal) => literal.to_string(),
        Expr::Logical { left, op, right } => {
            let left_str = format_ast(left);
            let right_str = format_ast(right);
            format!("({} {} {})", op.lexeme, left_str, right_str)
        }
        Expr::Unary { op, right } => {
            let right_str = format_ast(right);
            format!("({} {})", op.lexeme, right_str)
        }
        Expr::Variable(token) => token.lexeme.clone(),
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Stmt {
    Block(Vec<Stmt>),
    Expression(Expr),
    Function(Function),
    If { condition: Expr, then_branch: Box<Stmt>, else_branch: Option<Box<Stmt>> },
    Print(Expr),
    While { condition: Expr, body: Box<Stmt> },
    Var { name: Token, initializer: Option<Expr> },
    Return { keyword: Token, value: Option<Expr> },
}

#[derive(Clone, Debug, PartialEq)]
enum FunctionType {
    Function,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Function {
    pub name: Token,
    pub params: Vec<Token>,
    pub body: Vec<Stmt>,
}

impl Display for FunctionType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FunctionType::Function => write!(f, "function"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_format_ast() {
        let expr = Expr::Binary {
            left: Box::new(Expr::Unary {
                op: Token::new(TokenType::Minus, "-".to_string(), LiteralValue::None, 1),
                right: Box::new(Expr::Literal(LiteralValue::Number(123.0))),
            }),
            op: Token::new(TokenType::Star, "*".to_string(), LiteralValue::None, 1),
            right: Box::new(Expr::Grouping(Box::new(Expr::Literal(LiteralValue::Number(45.67))))),
        };

        let formated = format_ast(&expr);
        assert_eq!(formated, "(* (- 123) (group 45.67))");
    }
}

pub struct Parser {
    tokens: Vec<Token>,
    current: usize,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Parser {
        Parser { tokens, current: 0 }
    }

    pub fn parse(&mut self) -> Result<Vec<Stmt>> {
        let mut statements = Vec::<Stmt>::new();
        let mut errors = Vec::<Error>::new();
        while !self.is_at_end() {
            let statement = self.declaration();
            match statement {
                Ok(stmt) => statements.push(stmt),
                Err(err) => {
                    errors.push(err);
                    self.synchronize();
                }
            }
        }

        if errors.is_empty() {
            Ok(statements)
        } else {
            Err(anyhow::anyhow!("Parse errors: {:#?}", errors))
        }
    }

    fn declaration(&mut self) -> Result<Stmt> {
        if self.match_type(&[TokenType::Fun]) {
            self.function(FunctionType::Function)
        } else if self.match_type(&[TokenType::Var]) {
            self.var_declaration()
        } else {
            self.statement()
        }
    }

    fn function(&mut self, func_type: FunctionType) -> Result<Stmt> {
        let name =
            self.consume(TokenType::Identifier, &format!("Expect {} name.", func_type))?.clone();
        self.consume(TokenType::LeftParen, &format!("Expect '(' after {} name.", func_type))?;

        let mut params = Vec::<Token>::new();
        if !self.check(TokenType::RightParen) {
            loop {
                if params.len() >= 255 {
                    return Err(self.error(self.peek(), "Cannot have more than 255 parameters."));
                }

                params.push(self.consume(TokenType::Identifier, "Expect parameter name.")?.clone());

                if !self.match_type(&[TokenType::Comma]) {
                    break;
                }
            }
        }

        self.consume(TokenType::RightParen, "Expect ')' after parameters.")?;
        self.consume(TokenType::LeftBrace, &format!("Expect '{{' before {} body.", func_type))?;

        let body = self.block()?;

        Ok(Stmt::Function(Function { name, params, body }))
    }

    fn var_declaration(&mut self) -> Result<Stmt> {
        let name = self.consume(TokenType::Identifier, "Expect variable name.")?.clone();
        let initializer =
            if self.match_type(&[TokenType::Equal]) { Some(self.expression()?) } else { None };
        self.consume(TokenType::Semicolon, "Expect ';' after variable declaration.")?;
        Ok(Stmt::Var { name, initializer: initializer })
    }

    fn statement(&mut self) -> Result<Stmt> {
        if self.match_type(&[TokenType::For]) {
            return self.for_statement();
        }
        if self.match_type(&[TokenType::If]) {
            return self.if_statement();
        }
        if self.match_type(&[TokenType::Print]) {
            return self.print_statement();
        }
        if self.match_type(&[TokenType::Return]) {
            return self.return_statement();
        }
        if self.match_type(&[TokenType::While]) {
            return self.while_statement();
        }
        if self.match_type(&[TokenType::LeftBrace]) {
            return self.block().map(|statements| Stmt::Block(statements));
        }
        self.expression_statement()
    }

    fn for_statement(&mut self) -> Result<Stmt> {
        self.consume(TokenType::LeftParen, "Expect '(' after 'for'.")?;
        let initializer = if self.match_type(&[TokenType::Semicolon]) {
            None
        } else if self.match_type(&[TokenType::Var]) {
            Some(self.var_declaration()?)
        } else {
            Some(self.expression_statement()?)
        };

        let condition = if self.check(TokenType::Semicolon) {
            Expr::Literal(LiteralValue::True)
        } else {
            let cond = self.expression()?;
            self.consume(TokenType::Semicolon, "Expect ';' after loop condition.")?;
            cond
        };

        let increment =
            if self.check(TokenType::RightParen) { None } else { Some(self.expression()?) };

        self.consume(TokenType::RightParen, "Expect ')' after for clauses.")?;

        let mut body = self.statement()?;

        if let Some(increment) = increment {
            body = Stmt::Block(vec![body, Stmt::Expression(increment)]);
        }

        body = Stmt::While { condition, body: Box::new(body) };

        if let Some(initializer) = initializer {
            body = Stmt::Block(vec![initializer, body]);
        }

        Ok(body)
    }

    fn if_statement(&mut self) -> Result<Stmt> {
        self.consume(TokenType::LeftParen, "Expect '(' after 'if'.")?;
        let condition = self.expression()?;
        self.consume(TokenType::RightParen, "Expect ')' after if condition.")?;

        let then_branch = Box::new(self.statement()?);
        let else_branch = if self.match_type(&[TokenType::Else]) {
            Some(Box::new(self.statement()?))
        } else {
            None
        };

        Ok(Stmt::If { condition: condition, then_branch, else_branch })
    }

    fn block(&mut self) -> Result<Vec<Stmt>> {
        let mut statements = Vec::<Stmt>::new();

        while !self.check(TokenType::RightBrace) && !self.is_at_end() {
            statements.push(self.declaration()?);
        }

        self.consume(TokenType::RightBrace, "Expect '}' after block.")?;

        Ok(statements)
    }

    fn print_statement(&mut self) -> Result<Stmt> {
        let expr = self.expression()?;
        self.consume(TokenType::Semicolon, "Expect ';' after value.")?;
        Ok(Stmt::Print(expr))
    }

    fn return_statement(&mut self) -> Result<Stmt> {
        let keyword = self.previous().clone();
        let value = if self.check(TokenType::Semicolon) { None } else { Some(self.expression()?) };

        self.consume(TokenType::Semicolon, "Expect ';' after return value.")?;
        Ok(Stmt::Return { keyword, value })
    }

    fn while_statement(&mut self) -> Result<Stmt> {
        self.consume(TokenType::LeftParen, "Expect '(' after 'while'.")?;
        let condition = self.expression()?;
        self.consume(TokenType::RightParen, "Expect ')' after while condition.")?;

        let body = Box::new(self.statement()?);

        Ok(Stmt::While { condition, body })
    }

    fn expression_statement(&mut self) -> Result<Stmt> {
        let expr = self.expression()?;
        self.consume(TokenType::Semicolon, "Expect ';' after expression.")?;
        Ok(Stmt::Expression(expr))
    }

    fn expression(&mut self) -> Result<Expr> {
        self.assignment()
    }

    fn assignment(&mut self) -> Result<Expr> {
        let expr = self.or()?;

        if self.match_type(&[TokenType::Equal]) {
            let equals = self.previous().clone();
            let value = self.assignment()?;

            if let Expr::Variable(token) = expr {
                return Ok(Expr::Assign { name: token, value: Box::new(value) });
            }

            return Err(self.error(&equals, "Invalid assignment target."));
        }

        Ok(expr)
    }

    fn or(&mut self) -> Result<Expr> {
        let mut expr = self.and()?;

        while self.match_type(&[TokenType::Or]) {
            let op = self.previous().clone();
            let right = self.and()?;
            expr = Expr::Logical { left: Box::new(expr), op, right: Box::new(right) };
        }

        Ok(expr)
    }

    fn and(&mut self) -> Result<Expr> {
        let mut expr = self.equality()?;

        while self.match_type(&[TokenType::And]) {
            let op = self.previous().clone();
            let right = self.equality()?;
            expr = Expr::Logical { left: Box::new(expr), op, right: Box::new(right) };
        }

        Ok(expr)
    }

    fn equality(&mut self) -> Result<Expr> {
        let mut expr = self.comparison()?;

        while self.match_type(&[TokenType::BangEqual, TokenType::EqualEqual]) {
            let op = self.previous().clone();
            let right = self.comparison()?;
            expr = Expr::Binary { left: Box::new(expr), op, right: Box::new(right) };
        }

        Ok(expr)
    }

    fn comparison(&mut self) -> Result<Expr> {
        let mut expr = self.term()?;

        while self.match_type(&[
            TokenType::Greater,
            TokenType::GreaterEqual,
            TokenType::Less,
            TokenType::LessEqual,
        ]) {
            let op = self.previous().clone();
            let right = self.term()?;
            expr = Expr::Binary { left: Box::new(expr), op, right: Box::new(right) };
        }

        Ok(expr)
    }

    fn term(&mut self) -> Result<Expr> {
        let mut expr = self.factor()?;

        while self.match_type(&[TokenType::Minus, TokenType::Plus]) {
            let op = self.previous().clone();
            let right = self.factor()?;
            expr = Expr::Binary { left: Box::new(expr), op, right: Box::new(right) };
        }

        Ok(expr)
    }

    fn factor(&mut self) -> Result<Expr> {
        let mut expr = self.unary()?;
        while self.match_type(&[TokenType::Slash, TokenType::Star]) {
            let op = self.previous().clone();
            let right = self.unary()?;
            expr = Expr::Binary { left: Box::new(expr), op, right: Box::new(right) };
        }

        Ok(expr)
    }

    fn unary(&mut self) -> Result<Expr> {
        if self.match_type(&[TokenType::Bang, TokenType::Minus]) {
            let op = self.previous().clone();
            let right = self.unary()?;
            Ok(Expr::Unary { op, right: Box::new(right) })
        } else {
            self.call()
        }
    }

    fn call(&mut self) -> Result<Expr> {
        let mut expr = self.primary()?;

        loop {
            if self.match_type(&[TokenType::LeftParen]) {
                expr = self.finish_call(expr)?;
            } else {
                break;
            }
        }

        Ok(expr)
    }

    fn finish_call(&mut self, callee: Expr) -> Result<Expr> {
        let mut arguments = Vec::<Expr>::new();

        if !self.check(TokenType::RightParen) {
            loop {
                if arguments.len() >= 255 {
                    return Err(self.error(self.peek(), "Cannot have more than 255 arguments."));
                }

                arguments.push(self.expression()?);

                if !self.match_type(&[TokenType::Comma]) {
                    break;
                }
            }
        }

        let paren = self.consume(TokenType::RightParen, "Expect ')' after arguments.")?;
        Ok(Expr::Call { callee: Box::new(callee), paren: paren.clone(), arguments })
    }

    fn primary(&mut self) -> Result<Expr> {
        if self.match_type(&[TokenType::False]) {
            return Ok(Expr::Literal(LiteralValue::False));
        }
        if self.match_type(&[TokenType::True]) {
            return Ok(Expr::Literal(LiteralValue::True));
        }
        if self.match_type(&[TokenType::Nil]) {
            return Ok(Expr::Literal(LiteralValue::Nil));
        }
        if self.match_type(&[TokenType::Number]) {
            return Ok(Expr::Literal(self.previous().literal.clone()));
        }
        if self.match_type(&[TokenType::String]) {
            return Ok(Expr::Literal(self.previous().literal.clone()));
        }
        if self.match_type(&[TokenType::Identifier]) {
            return Ok(Expr::Variable(self.previous().clone()));
        }

        if self.match_type(&[TokenType::LeftParen]) {
            let expr = self.expression()?;
            self.consume(TokenType::RightParen, "Expect ')' after expression.")?;
            return Ok(Expr::Grouping(Box::new(expr)));
        }

        Err(self.error(self.peek(), "Expect expression."))
    }

    fn match_type(&mut self, token_types: &[TokenType]) -> bool {
        for token_type in token_types {
            if self.check(token_type.clone()) {
                self.advance();
                return true;
            }
        }
        false
    }

    fn check(&self, token_type: TokenType) -> bool {
        if self.is_at_end() {
            false
        } else {
            self.peek().token_type == token_type
        }
    }

    fn is_at_end(&self) -> bool {
        self.peek().token_type == TokenType::Eof
    }

    fn peek(&self) -> &Token {
        &self.tokens[self.current]
    }

    fn previous(&self) -> &Token {
        &self.tokens[self.current - 1]
    }

    fn advance(&mut self) -> &Token {
        if !self.is_at_end() {
            self.current += 1;
        }
        &self.previous()
    }

    fn consume(&mut self, token_type: TokenType, message: &str) -> Result<&Token> {
        if self.check(token_type) {
            Ok(self.advance())
        } else {
            Err(self.error(self.peek(), message))
        }
    }

    fn error(&self, token: &Token, message: &str) -> Error {
        match token.token_type {
            TokenType::Eof => anyhow::anyhow!("Line: {}: at end: {}", token.line, message),
            _ => anyhow::anyhow!("Line: {}: at '{}': {}", token.line, token.lexeme, message),
        }
    }

    fn synchronize(&mut self) {
        self.advance();

        while !self.is_at_end() {
            if self.previous().token_type == TokenType::Semicolon {
                return;
            }

            match self.peek().token_type {
                TokenType::Class |
                TokenType::Fun |
                TokenType::Var |
                TokenType::For |
                TokenType::If |
                TokenType::While |
                TokenType::Print |
                TokenType::Return => {
                    break;
                }
                _ => {}
            }

            self.advance();
        }
    }
}
