use std::fmt::{self, Display, Formatter};

use crate::lox::chunk::{Chunk, OpCode};
use crate::lox::debug::disassemble_instruction;
use crate::lox::value::Value;

pub struct VM {
    chunk: Chunk,
    ip: usize,
    stack: Vec<Value>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InterpretResult {
    Ok,
    CompileError,
    RuntimeError,
}

impl Display for InterpretResult {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            InterpretResult::Ok => write!(f, "Ok"),
            InterpretResult::CompileError => write!(f, "CompileError"),
            InterpretResult::RuntimeError => write!(f, "RuntimeError"),
        }
    }
}

macro_rules! binary_op {
    ($self:ident, $op:tt) => {
        {
            let b = $self.pop();
            let a = $self.pop();
            $self.push(a $op b);
        }
    };
}

impl VM {
    pub fn new() -> VM {
        VM { chunk: Chunk::new(), ip: 0, stack: Vec::with_capacity(256) }
    }

    pub fn interpret(&mut self, chunk: Chunk) -> InterpretResult {
        debug_assert!(!chunk.code.is_empty());
        // chunk is guaranteed to have at least one byte. And it won't change in the lifetime of VM.
        // So it's safe to get pointer to the code.

        self.ip = 0;
        self.chunk = chunk;
        self.run()
    }

    fn run(&mut self) -> InterpretResult {
        loop {
            #[cfg(debug_trace_execution)]
            {
                print!("          ");
                for value in &self.stack {
                    print!("[ {} ]", value);
                }
                println!();
                disassemble_instruction(&self.chunk, self.ip);
            }

            match OpCode(self.read_byte()) {
                OpCode::OP_CONSTANT => {
                    let constant = self.read_const();
                    self.push(constant);
                }
                OpCode::OP_ADD => binary_op!(self, +),
                OpCode::OP_SUBTRACT => binary_op!(self, -),
                OpCode::OP_MULTIPLY => binary_op!(self, *),
                OpCode::OP_DIVIDE => binary_op!(self, /),
                OpCode::OP_NEGATE => {
                    let value = self.pop();
                    self.push(-value);
                }
                OpCode::OP_RETURN => {
                    let value = self.pop();
                    self.print_value(value);
                    println!();
                    return InterpretResult::Ok;
                }
                _ => {}
            }
        }
    }

    fn read_byte(&mut self) -> u8 {
        let byte = self.chunk.code[self.ip];
        self.ip = self.ip + 1;
        byte
    }

    fn read_const(&mut self) -> Value {
        let index = self.read_byte() as usize;
        self.chunk.constants[index]
    }

    fn print_value(&self, value: Value) {
        print!("{}", value);
    }

    fn push(&mut self, value: Value) {
        self.stack.push(value);
    }

    fn pop(&mut self) -> Value {
        self.stack.pop().unwrap()
    }
}
