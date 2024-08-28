mod lox;

use std::io::{self, Write};

use crate::lox::compiler::Compiler;
use crate::lox::vm::{InterpretResult, VM};

use anyhow::Result;

fn main() {
    let args = std::env::args().collect::<Vec<String>>();
    if args.len() == 1 {
        repl();
    } else if args.len() == 2 {
        run_file(&args[1]);
    } else {
        eprintln!("Usage: lox [path]");
        std::process::exit(64);
    }
}

fn repl() {
    let mut vm = VM::new();
    loop {
        print!("> ");
        io::stdout().flush().unwrap();
        let mut line = String::new();
        io::stdin().read_line(&mut line).unwrap();
        if line.is_empty() {
            break;
        }

        interpret(&line, &mut vm);
    }
}

fn run_file(path: &str) {
    let source = match std::fs::read_to_string(path) {
        Ok(source) => source,
        Err(e) => {
            eprintln!("Failed to read file: {}", e);
            std::process::exit(74);
        }
    };

    let mut vm = VM::new();
    if let Err(e) = interpret(&source, &mut vm) {
        if e.downcast::<InterpretResult>().unwrap() == InterpretResult::CompileError {
            std::process::exit(65);
        } else {
            std::process::exit(70);
        }
    }
}

fn interpret(source: &str, _vm: &mut VM) -> Result<()> {
    let mut compiler = Compiler::new(source);
    compiler.compile();
    Ok(())
}
