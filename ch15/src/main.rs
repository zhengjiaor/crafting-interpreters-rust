mod lox;

use lox::chunk::OpCode;

use crate::lox::chunk::Chunk;
use crate::lox::vm::VM;

fn main() {
    let mut vm = VM::new();

    let mut chunk = Chunk::new();

    let constant = chunk.add_constant(1.2);
    chunk.write_opcode(lox::chunk::OpCode::OP_CONSTANT, 123);
    chunk.write_byte(constant as u8, 123);

    let constant = chunk.add_constant(3.4);
    chunk.write_opcode(lox::chunk::OpCode::OP_CONSTANT, 123);
    chunk.write_byte(constant as u8, 123);

    chunk.write_opcode(lox::chunk::OpCode::OP_ADD, 123);

    let constant = chunk.add_constant(5.6);
    chunk.write_opcode(lox::chunk::OpCode::OP_CONSTANT, 123);
    chunk.write_byte(constant as u8, 123);

    chunk.write_opcode(lox::chunk::OpCode::OP_DIVIDE, 123);
    chunk.write_opcode(OpCode::OP_NEGATE, 123);

    chunk.write_opcode(lox::chunk::OpCode::OP_RETURN, 123);

    vm.interpret(chunk);
}
