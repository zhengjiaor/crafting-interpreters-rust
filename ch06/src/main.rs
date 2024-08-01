use std::{
    env, fs,
    io::{self, Write},
    process,
};

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
    run(source).expect("Failed to scan tokens");
}

fn run_prompt() {
    loop {
        print!("> ");
        io::stdout().flush().unwrap();
        let mut line = String::new();
        io::stdin().read_line(&mut line).unwrap();
        if line.is_empty() {
            break;
        }

        if let Err(e) = run(line) {
            eprintln!("{}", e);
        }
    }
}

fn run(source: String) -> anyhow::Result<()> {
    let result = lox::scanner::Scanner::new(source).scan_tokens()?;
    for token in &result {
        println!("{:?}", token);
    }
    let expression = lox::parser::Parser::new(result).parse()?;
    Ok(println!("[ast]: {}", lox::parser::format_ast(&expression)))
}
