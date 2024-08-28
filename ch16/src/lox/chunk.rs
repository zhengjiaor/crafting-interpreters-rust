use crate::lox::value::Value;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OpCode(pub u8);

impl OpCode {
    pub const OP_CONSTANT: OpCode = OpCode(0);
    pub const OP_ADD: OpCode = OpCode(1);
    pub const OP_SUBTRACT: OpCode = OpCode(2);
    pub const OP_MULTIPLY: OpCode = OpCode(3);
    pub const OP_DIVIDE: OpCode = OpCode(4);
    pub const OP_NEGATE: OpCode = OpCode(5);
    pub const OP_RETURN: OpCode = OpCode(6);
}

pub struct Chunk {
    pub code: Vec<u8>,
    pub lines: Vec<usize>,
    pub constants: Vec<Value>,
}

impl Chunk {
    pub fn new() -> Chunk {
        Chunk { code: Vec::new(), lines: Vec::new(), constants: Vec::new() }
    }

    pub fn len(&self) -> usize {
        self.code.len()
    }

    pub fn write_opcode(&mut self, op_code: OpCode, line: usize) {
        self.code.push(op_code.0);
        self.lines.push(line);
    }

    pub fn write_byte(&mut self, byte: u8, line: usize) {
        self.code.push(byte);
        self.lines.push(line);
    }

    pub fn add_constant(&mut self, value: Value) -> usize {
        self.constants.push(value);
        self.constants.len() - 1
    }
}
