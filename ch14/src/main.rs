mod lox;

use crate::lox::chunk::Chunk;
use crate::lox::debug::disassemble_chunk;

fn main() {
    let mut chunk = Chunk::new();

    let constant = chunk.add_constant(1.2);
    chunk.write_opcode(lox::chunk::OpCode::OP_CONSTANT, 123);
    chunk.write_byte(constant as u8, 123);

    chunk.write_opcode(lox::chunk::OpCode::OP_RETURN, 123);

    disassemble_chunk(&chunk, "test chunk");
}
