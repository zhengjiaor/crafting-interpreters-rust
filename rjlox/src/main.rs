use std::{
    env, fs,
    io::{self, Write},
    process,
};

use lox::{interpreter, parser, resolver, scanner};

mod lox;

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    if args.len() > 1 {
        println!("Usage: jlox [script]");
        process::exit(64);
    } else if args.len() == 1 {
        run_file(&args[0]);
    } else {
        run_prompt();
    }
}

fn run_file(path: &str) {
    let source = fs::read_to_string(path).expect(format!("Failed to read file: {}", path).as_str());
    run(source, &mut interpreter::Interpreter::new());
}

fn run_prompt() {
    let mut interpreter = interpreter::Interpreter::new();
    loop {
        print!("> ");
        io::stdout().flush().unwrap();
        let mut line = String::new();
        io::stdin().read_line(&mut line).unwrap();
        if line.is_empty() {
            break;
        }

        run(line, &mut interpreter)
    }
}

fn run(source: String, interpreter: &mut interpreter::Interpreter) {
    let mut scanner = scanner::Scanner::new(source);
    let tokens = match scanner.scan_tokens() {
        Ok(tokens) => tokens,
        Err(_) => {
            process::exit(65);
        }
    };

    let statements = match parser::Parser::new(tokens).parse() {
        Ok(statements) => statements,
        Err(_) => process::exit(65),
    };

    if scanner.had_error {
        process::exit(65);
    }

    let mut resolver = resolver::Resolver::new(interpreter);
    if let Err(_) = resolver.resolve(&statements) {
        process::exit(65);
    }

    if let Err(_) = interpreter.interpret(statements) {
        process::exit(70);
    }
}
