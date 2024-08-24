use crate::lox::chunk::{Chunk, OpCode};

pub fn disassemble_chunk(chunk: &Chunk, name: &str) {
    println!("== {} ==", name);

    let mut offset = 0;
    while offset < chunk.len() {
        offset = disassemble_instruction(chunk, offset);
    }
}

fn disassemble_instruction(chunk: &Chunk, offset: usize) -> usize {
    print!("{:04} ", offset);
    if (offset > 0) && (chunk.lines[offset] == chunk.lines[offset - 1]) {
        print!("   | ");
    } else {
        print!("{:4} ", chunk.lines[offset]);
    }

    let byte = chunk.code[offset];
    let instruction = OpCode(byte);
    match instruction {
        OpCode::OP_RETURN => simple_instruction("OP_RETURN", offset),
        OpCode::OP_CONSTANT => constant_instruction("OP_CONSTANT", offset, chunk),
        _ => {
            println!("Unknown opcode {}", byte);
            offset + 1
        }
    }
}

fn simple_instruction(name: &str, offset: usize) -> usize {
    println!("{}", name);
    offset + 1
}

fn constant_instruction(name: &str, offset: usize, chunk: &Chunk) -> usize {
    let constant = chunk.code[offset + 1];
    println!("{:<16} {:4} '{}'", name, constant, chunk.constants[constant as usize]);
    offset + 2
}
