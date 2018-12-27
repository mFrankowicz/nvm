use crate::opcode::{OPCODE, SEGMENT, TYPE};
use byteorder::*;

use byteorder::BigEndian;
use std::io::Cursor;

#[derive(Default, Clone)]
pub struct PICOVM {
    registers: [u64; 32],
    program: Vec<u8>,
    stack: Vec<u8>,
    mem: MEMORY,
    pc: usize,
    sp: usize,
    flags: u8,
}

#[derive(Default, Clone)]
pub struct MEMORY {
    local: Box<Vec<u8>>,
    argument: Box<Vec<u8>>,
    this: Box<Vec<u8>>,
    that: Box<Vec<u8>>,
    sttic: Box<Vec<u8>>,
    pointer: Box<Vec<u8>>,
    temp: Box<Vec<u8>>,
}

impl MEMORY {
    pub fn new() -> Self {
        MEMORY {
            local: Box::new(Vec::with_capacity(32000)),
            argument: Box::new(Vec::with_capacity(32000)),
            this: Box::new(Vec::with_capacity(32000)),
            that: Box::new(Vec::with_capacity(32000)),
            sttic:Box::new(Vec::with_capacity(32000)),
            pointer:Box::new(Vec::with_capacity(32000)),
            temp: Box::new(Vec::with_capacity(32000)),
        }
    }
}

impl PICOVM {
    pub fn new() -> Self {
        PICOVM {
            registers: [0; 32],
            program: Vec::new(),
            stack: Vec::with_capacity(1024),
            mem: MEMORY::new(),
            pc: 0,
            sp: 0,
            flags: 0,
        }
    }

    pub fn run_once(&mut self) {
        self.process_instruction();
    }

    fn process_instruction(&mut self) -> Option<u8> {
        if self.pc > self.program.len() {
            return Some(1);
        }

        match self.fetch_opcode() {
            OPCODE::HLT => {
                return Some(self.flags);
            }
            OPCODE::IGL => {
                return Some(1);
            }
            OPCODE::PUSH(seg) => {
                match seg {
                    SEGMENT::CONSTANT => {
                        let vmtype = self.next_8_bits();
                        self.next_8_bits();
                        match TYPE::from(vmtype) {
                            TYPE::U8 => {
                                let value = self.next_8_bits();
                                self.stack.push(value);
                                self.sp += 1;
                            }
                            TYPE::U16 => {
                                let value = self.next_16_bits();
                                self.stack.write_u16::<BigEndian>(value).unwrap();
                                self.sp += 2;
                            }
                            TYPE::U32 => {
                                let value = self.next_32_bits();
                                self.stack.write_u32::<BigEndian>(value).unwrap();
                                self.sp += 4;
                            }
                            TYPE::U64 => {
                                let value = self.next_64_bits();
                                self.stack.write_u64::<BigEndian>(value).unwrap();
                                self.sp += 8;
                            }
                            TYPE::I8 => {
                                self.push_i8();
                                self.sp += 1;
                            }
                            TYPE::I16 => {
                                self.push_i16();
                                self.sp += 2;
                            }
                            TYPE::I32 => {
                                self.push_i32();
                                self.sp += 4;
                            }
                            TYPE::I64 => {
                                self.push_i64();
                                self.sp += 8;
                            }
                            TYPE::F32 => {
                                self.push_f32();
                                self.sp += 4;
                            }
                            TYPE::F64 => {
                                self.push_f64();
                                self.sp += 8;
                            }
                            _ => {
                                return Some(1);
                            }
                        }
                    },
                    _ => {
                        self.push_segment(seg);
                    }
                }
            }
            OPCODE::POP(seg) => match seg {
                SEGMENT::LOCAL => {
                    let index = self.next_8_bits();
                    if let Some(value) = self.stack.pop() {
                        self.mem.local[index as usize] = value;
                        self.sp -= 1;
                        self.next_8_bits();
                    } else {
                        return Some(1);
                    };
                }
                SEGMENT::ARGUMENT => {
                    let index = self.next_8_bits();
                    if let Some(value) = self.stack.pop() {
                        self.mem.argument[index as usize] = value;
                        self.sp -= 1;
                        self.next_8_bits();
                    } else {
                        return Some(1);
                    };
                }
                SEGMENT::THIS => {
                    let index = self.next_8_bits();
                    if let Some(value) = self.stack.pop() {
                        self.mem.this[index as usize] = value;
                        self.sp -= 1;
                        self.next_8_bits();
                    } else {
                        return Some(1);
                    };
                }
                SEGMENT::THAT => {
                    let index = self.next_8_bits();
                    if let Some(value) = self.stack.pop() {
                        self.mem.that[index as usize] = value;
                        self.sp -= 1;
                        self.next_8_bits();
                    } else {
                        return Some(1);
                    };
                }
                SEGMENT::STATIC => {
                    let index = self.next_8_bits();
                    if let Some(value) = self.stack.pop() {
                        self.mem.sttic[index as usize] = value;
                        self.sp -= 1;
                        self.next_8_bits();
                    } else {
                        return Some(1);
                    };
                }
                SEGMENT::POINTER => {
                    let index = self.next_8_bits();
                    if let Some(value) = self.stack.pop() {
                        self.mem.pointer[index as usize] = value;
                        self.sp -= 1;
                        self.next_8_bits();
                    } else {
                        return Some(1);
                    };
                }
                SEGMENT::TEMP => {
                    let index = self.next_8_bits();
                    if let Some(value) = self.stack.pop() {
                        self.mem.temp[index as usize] = value;
                        self.sp -= 1;
                        self.next_8_bits();
                    } else {
                        return Some(1);
                    };
                }
                SEGMENT::CONSTANT => {
                    return Some(1);
                }
                SEGMENT::IGL => {
                    return Some(1);
                }
            },
            OPCODE::ADD => {
                let x = self.stack.pop().unwrap_or_default();
                let y = self.stack.pop().unwrap_or_default();
                let res = x + y;
                self.sp -= 1;
                self.stack.push(res);
                self.next_16_bits();
            }
            OPCODE::SUB => {
                let x = self.stack.pop().unwrap_or_default();
                let y = self.stack.pop().unwrap_or_default();
                let res = x - y;
                self.sp -= 1;
                self.stack.push(res);
                self.next_16_bits();
            }
            OPCODE::MUL => {
                let x = self.stack.pop().unwrap_or_default();
                let y = self.stack.pop().unwrap_or_default();
                let res = x * y;
                self.sp -= 1;
                self.stack.push(res);
                self.next_16_bits();
            }
            OPCODE::DIV => {
                let x = self.stack.pop().unwrap_or_default();
                let y = self.stack.pop().unwrap_or_default();
                let res = x / y;
                self.sp -= 1;
                self.stack.push(res);
                self.next_16_bits();
            }
            OPCODE::MOD => {
                let x = self.stack.pop().unwrap_or_default();
                let y = self.stack.pop().unwrap_or_default();
                let res = x % y;
                self.sp -= 1;
                self.stack.push(res);
                self.next_16_bits();
            }
            OPCODE::EQ => {
                let x = self.stack.pop().unwrap_or_default();
                let y = self.stack.pop().unwrap_or_default();
                let res = x == y;
                if res {
                    self.stack.push(1);
                } else {
                    self.stack.push(0);
                }
                self.sp -= 1;

                self.next_16_bits();
            }
            OPCODE::NEQ => {
                let x = self.stack.pop().unwrap_or_default();
                let y = self.stack.pop().unwrap_or_default();
                let res = x != y;
                if res {
                    self.stack.push(1);
                } else {
                    self.stack.push(0);
                }
                self.sp -= 1;

                self.next_16_bits();
            }
            OPCODE::LT => {
                let x = self.stack.pop().unwrap_or_default();
                let y = self.stack.pop().unwrap_or_default();
                let res = x < y;
                if res {
                    self.stack.push(1);
                } else {
                    self.stack.push(0);
                }
                self.sp -= 1;

                self.next_16_bits();
            }
            OPCODE::LTE => {
                let x = self.stack.pop().unwrap_or_default();
                let y = self.stack.pop().unwrap_or_default();
                let res = x <= y;
                if res {
                    self.stack.push(1);
                } else {
                    self.stack.push(0);
                }
                self.sp -= 1;

                self.next_16_bits();
            }
            OPCODE::GT => {
                let x = self.stack.pop().unwrap_or_default();
                let y = self.stack.pop().unwrap_or_default();
                let res = x > y;
                if res {
                    self.stack.push(1);
                } else {
                    self.stack.push(0);
                }
                self.sp -= 1;

                self.next_16_bits();
            }
            OPCODE::GTE => {
                let x = self.stack.pop().unwrap_or_default();
                let y = self.stack.pop().unwrap_or_default();
                let res = x >= y;
                if res {
                    self.stack.push(1);
                } else {
                    self.stack.push(0);
                }
                self.sp -= 1;

                self.next_16_bits();
            }
            OPCODE::AND => {
                let x = self.stack.pop().unwrap_or_default();
                let y = self.stack.pop().unwrap_or_default();
                let res = x & y;
                self.stack.push(res);
                self.sp -= 1;
                self.next_16_bits();
            }
            OPCODE::OR => {
                let x = self.stack.pop().unwrap_or_default();
                let y = self.stack.pop().unwrap_or_default();
                let res = x | y;
                self.stack.push(res);
                self.sp -= 1;
                self.next_16_bits();
            }
            OPCODE::XOR => {
                let x = self.stack.pop().unwrap_or_default();
                let y = self.stack.pop().unwrap_or_default();
                let res = x ^ y;
                self.stack.push(res);
                self.sp -= 1;
                self.next_16_bits();
            }
            OPCODE::NOT => {
                let x = self.stack.pop().unwrap_or_default();
                let res = !x;
                self.stack.push(res);

                self.next_16_bits();
            }
        }
        None
    }

    fn fetch_opcode(&mut self) -> OPCODE {
        let opcode = OPCODE::from((self.program[self.pc], self.program[self.pc + 1]));
        self.pc += 2;
        opcode
    }

    fn next_8_bits(&mut self) -> u8 {
        let result = self.program[self.pc];
        self.pc += 1;
        result
    }

    fn next_byte(&mut self) -> Cursor<[u8; 1]> {
        let res = [self.program[self.pc]];
        self.pc += 1;
        Cursor::new(res)
    }

    fn next_16_bits(&mut self) -> u16 {
        let result =
            ((u16::from(self.program[self.pc])) << 8) | u16::from(self.program[self.pc + 1]);
        self.pc += 2;
        result
    }

    fn next_2_bytes_be(&mut self) -> Cursor<[u8; 2]> {
        let res = [self.program[self.pc], self.program[self.pc + 1]];
        self.pc += 2;
        Cursor::new(res)
    }

    fn next_32_bits(&mut self) -> u32 {
        let result = ((u32::from(self.program[self.pc])) << 24)
            | ((u32::from(self.program[self.pc + 1])) << 16)
            | ((u32::from(self.program[self.pc + 2])) << 8)
            | u32::from(self.program[self.pc + 3]);
        self.pc += 4;
        result
    }

    fn next_4_bytes_be(&mut self) -> Cursor<[u8; 4]> {
        let res = [
            self.program[self.pc],
            self.program[self.pc + 1],
            self.program[self.pc + 2],
            self.program[self.pc + 3],
        ];
        self.pc += 4;
        Cursor::new(res)
    }

    fn next_64_bits(&mut self) -> u64 {
        let result = ((u64::from(self.program[self.pc])) << 56)
            | ((u64::from(self.program[self.pc + 1])) << 48)
            | ((u64::from(self.program[self.pc + 2])) << 40)
            | ((u64::from(self.program[self.pc + 3])) << 32)
            | ((u64::from(self.program[self.pc + 4])) << 24)
            | ((u64::from(self.program[self.pc + 5])) << 16)
            | ((u64::from(self.program[self.pc + 6])) << 8)
            | u64::from(self.program[self.pc + 7]);
        self.pc += 8;
        result
    }

    fn next_8_bytes_be(&mut self) -> Cursor<[u8; 8]> {
        let res = [
            self.program[self.pc],
            self.program[self.pc + 1],
            self.program[self.pc + 2],
            self.program[self.pc + 3],
            self.program[self.pc + 4],
            self.program[self.pc + 5],
            self.program[self.pc + 6],
            self.program[self.pc + 7],
        ];
        self.pc += 8;
        Cursor::new(res)
    }
}

impl PICOVM {

    pub fn push_i8(&mut self) {
        let mut value = self.next_byte();
        self.stack.write_i8(value.read_i8().unwrap()).unwrap();
    }

    pub fn push_u16(&mut self) {
        let mut value = self.next_2_bytes_be();
        self.stack.write_u16::<BigEndian>(value.read_u16::<BigEndian>().unwrap()).unwrap();
    }

    pub fn push_i16(&mut self) {
        let mut value = self.next_2_bytes_be();
        self.stack.write_i16::<BigEndian>(value.read_i16::<BigEndian>().unwrap()).unwrap();
    }

    pub fn push_u32(&mut self) {
        let mut value = self.next_4_bytes_be();
        self.stack.write_u32::<BigEndian>(value.read_u32::<BigEndian>().unwrap()).unwrap();
    }

    pub fn push_i32(&mut self) {
        let mut value = self.next_4_bytes_be();
        self.stack.write_i32::<BigEndian>(value.read_i32::<BigEndian>().unwrap()).unwrap();
    }

    pub fn push_u64(&mut self) {
        let mut value = self.next_8_bytes_be();
        self.stack.write_u64::<BigEndian>(value.read_u64::<BigEndian>().unwrap()).unwrap();
    }

    pub fn push_i64(&mut self) {
        let mut value = self.next_8_bytes_be();
        self.stack.write_i64::<BigEndian>(value.read_i64::<BigEndian>().unwrap()).unwrap();
    }

    pub fn push_f32(&mut self) {
        let mut value = self.next_4_bytes_be();
        self.stack.write_f32::<BigEndian>(value.read_f32::<BigEndian>().unwrap()).unwrap();
    }

    pub fn push_f64(&mut self) {
        let mut value = self.next_8_bytes_be();
        self.stack.write_f64::<BigEndian>(value.read_f64::<BigEndian>().unwrap()).unwrap();
    }

    pub fn push_segment(&mut self, segment: SEGMENT) {
        let vmtype = self.next_8_bits();
        self.next_8_bits();
        match TYPE::from(vmtype) {
            TYPE::U8 => self.push_segment_u8(segment),
            TYPE::I8 => self.push_segment_i8(segment),
            TYPE::U16 => self.push_segment_u16(segment),
            TYPE::I16 => self.push_segment_i16(segment),
            TYPE::U32 => self.push_segment_u32(segment),
            TYPE::I32 => self.push_segment_i32(segment),
            TYPE::U64 => self.push_segment_u64(segment),
            TYPE::I64 => self.push_segment_i64(segment),
            TYPE::F32 => self.push_segment_f32(segment),
            TYPE::F64 => self.push_segment_f64(segment),
            _ => {}
        }
    }

    /// [PUSH, SEGMENT, TYPE, 0,
    /// INDEX, INDEX, INDEX, INDEX]
    pub fn push_segment_u8(&mut self, segment: SEGMENT) {
        let index = self.next_32_bits() as usize;
        match segment {
            SEGMENT::LOCAL => {
                let value = Cursor::new(vec![self.mem.local[index]]).read_u8().unwrap();
                self.stack.write_u8(value).unwrap();
            },
            SEGMENT::ARGUMENT => {
                let value = Cursor::new(vec![self.mem.argument[index]]).read_u8().unwrap();
                self.stack.write_u8(value).unwrap();
            },
            SEGMENT::STATIC => {
                let value = Cursor::new(vec![self.mem.sttic[index]]).read_u8().unwrap();
                self.stack.write_u8(value).unwrap();
            },
            SEGMENT::TEMP => {
                let value = Cursor::new(vec![self.mem.temp[index]]).read_u8().unwrap();
                self.stack.write_u8(value).unwrap();
            },
            SEGMENT::THIS => {
                let value = Cursor::new(vec![self.mem.this[index]]).read_u8().unwrap();
                self.stack.write_u8(value).unwrap();
            },
            SEGMENT::THAT => {
                let value = Cursor::new(vec![self.mem.that[index]]).read_u8().unwrap();
                self.stack.write_u8(value).unwrap();
            },
            SEGMENT::POINTER => {
                let value = Cursor::new(vec![self.mem.pointer[index]]).read_u8().unwrap();
                self.stack.write_u8(value).unwrap();
            },
            _ => {

            }
        }

        self.sp += 1;
    }

    /// [PUSH, SEGMENT, TYPE, 0,
    /// INDEX, INDEX, INDEX, INDEX]
    pub fn push_segment_i8(&mut self, segment: SEGMENT) {
        let index = self.next_32_bits() as usize;
        match segment {
            SEGMENT::LOCAL => {
                let value = Cursor::new(vec![self.mem.local[index]]).read_i8().unwrap();
                self.stack.write_i8(value).unwrap();
            },
            SEGMENT::ARGUMENT => {
                let value = Cursor::new(vec![self.mem.argument[index]]).read_i8().unwrap();
                self.stack.write_i8(value).unwrap();
            },
            SEGMENT::STATIC => {
                let value = Cursor::new(vec![self.mem.sttic[index]]).read_i8().unwrap();
                self.stack.write_i8(value).unwrap();
            },
            SEGMENT::TEMP => {
                let value = Cursor::new(vec![self.mem.temp[index]]).read_i8().unwrap();
                self.stack.write_i8(value).unwrap();
            },
            SEGMENT::THIS => {
                let value = Cursor::new(vec![self.mem.this[index]]).read_i8().unwrap();
                self.stack.write_i8(value).unwrap();
            },
            SEGMENT::THAT => {
                let value = Cursor::new(vec![self.mem.that[index]]).read_i8().unwrap();
                self.stack.write_i8(value).unwrap();
            },
            SEGMENT::POINTER => {
                let value = Cursor::new(vec![self.mem.pointer[index]]).read_i8().unwrap();
                self.stack.write_i8(value).unwrap();
            },
            _ => {

            }
        }

        self.sp += 1;
    }

    /// [PUSH, SEGMENT, TYPE, 0,
    /// INDEX, INDEX, INDEX, INDEX]
    pub fn push_segment_u16(&mut self, segment: SEGMENT) {
        let index = self.next_32_bits() as usize;
        match segment {
            SEGMENT::LOCAL => {
                let value = Cursor::new(vec![self.mem.local[index], self.mem.local[index+1]]).read_u16::<BigEndian>().unwrap();
                self.stack.write_u16::<BigEndian>(value).unwrap();
            },
            SEGMENT::ARGUMENT => {
                let value = Cursor::new(vec![self.mem.argument[index], self.mem.argument[index+1]]).read_u16::<BigEndian>().unwrap();
                self.stack.write_u16::<BigEndian>(value).unwrap();
            },
            SEGMENT::STATIC => {
                let value = Cursor::new(vec![self.mem.sttic[index], self.mem.sttic[index+1]]).read_u16::<BigEndian>().unwrap();
                self.stack.write_u16::<BigEndian>(value).unwrap();
            },
            SEGMENT::TEMP => {
                let value = Cursor::new(vec![self.mem.temp[index], self.mem.temp[index+1]]).read_u16::<BigEndian>().unwrap();
                self.stack.write_u16::<BigEndian>(value).unwrap();
            },
            SEGMENT::THIS => {
                let value = Cursor::new(vec![self.mem.this[index], self.mem.this[index+1]]).read_u16::<BigEndian>().unwrap();
                self.stack.write_u16::<BigEndian>(value).unwrap();
            },
            SEGMENT::THAT => {
                let value = Cursor::new(vec![self.mem.that[index], self.mem.that[index]]).read_u16::<BigEndian>().unwrap();
                self.stack.write_u16::<BigEndian>(value).unwrap();
            },
            SEGMENT::POINTER => {
                let value = Cursor::new(vec![self.mem.pointer[index], self.mem.pointer[index]]).read_u16::<BigEndian>().unwrap();
                self.stack.write_u16::<BigEndian>(value).unwrap();
            },
            _ => {

            }
        }

        self.sp += 2;
    }

    /// [PUSH, SEGMENT, TYPE, 0,
    /// INDEX, INDEX, INDEX, INDEX]
    pub fn push_segment_i16(&mut self, segment: SEGMENT) {
        let index = self.next_32_bits() as usize;
        match segment {
            SEGMENT::LOCAL => {
                let value = Cursor::new(vec![self.mem.local[index], self.mem.local[index+1]]).read_i16::<BigEndian>().unwrap();
                self.stack.write_i16::<BigEndian>(value).unwrap();
            },
            SEGMENT::ARGUMENT => {
                let value = Cursor::new(vec![self.mem.argument[index], self.mem.argument[index+1]]).read_i16::<BigEndian>().unwrap();
                self.stack.write_i16::<BigEndian>(value).unwrap();
            },
            SEGMENT::STATIC => {
                let value = Cursor::new(vec![self.mem.sttic[index], self.mem.sttic[index+1]]).read_i16::<BigEndian>().unwrap();
                self.stack.write_i16::<BigEndian>(value).unwrap();
            },
            SEGMENT::TEMP => {
                let value = Cursor::new(vec![self.mem.temp[index], self.mem.temp[index+1]]).read_i16::<BigEndian>().unwrap();
                self.stack.write_i16::<BigEndian>(value).unwrap();
            },
            SEGMENT::THIS => {
                let value = Cursor::new(vec![self.mem.this[index], self.mem.this[index+1]]).read_i16::<BigEndian>().unwrap();
                self.stack.write_i16::<BigEndian>(value).unwrap();
            },
            SEGMENT::THAT => {
                let value = Cursor::new(vec![self.mem.that[index], self.mem.that[index]]).read_i16::<BigEndian>().unwrap();
                self.stack.write_i16::<BigEndian>(value).unwrap();
            },
            SEGMENT::POINTER => {
                let value = Cursor::new(vec![self.mem.pointer[index], self.mem.pointer[index]]).read_i16::<BigEndian>().unwrap();
                self.stack.write_i16::<BigEndian>(value).unwrap();
            },
            _ => {

            }
        }

        self.sp += 2;
    }

    /// [PUSH, SEGMENT, TYPE, 0,
    /// INDEX, INDEX, INDEX, INDEX]
    pub fn push_segment_u32(&mut self, segment: SEGMENT) {
        let index = self.next_32_bits() as usize;
        match segment {
            SEGMENT::LOCAL => {
                let value = Cursor::new(vec![
                    self.mem.local[index],
                    self.mem.local[index+1],
                    self.mem.local[index+2],
                    self.mem.local[index+3]]
                ).read_u32::<BigEndian>().unwrap();
                self.stack.write_u32::<BigEndian>(value).unwrap();
            },
            SEGMENT::ARGUMENT => {
                let value = Cursor::new(vec![
                    self.mem.argument[index],
                    self.mem.argument[index+1],
                    self.mem.argument[index+2],
                    self.mem.argument[index+3]]
                ).read_u32::<BigEndian>().unwrap();
                self.stack.write_u32::<BigEndian>(value).unwrap();
            },
            SEGMENT::STATIC => {
                let value = Cursor::new(vec![
                    self.mem.sttic[index],
                    self.mem.sttic[index+1],
                    self.mem.sttic[index+2],
                    self.mem.sttic[index+3]]
                ).read_u32::<BigEndian>().unwrap();
                self.stack.write_u32::<BigEndian>(value).unwrap();
            },
            SEGMENT::TEMP => {
                let value = Cursor::new(vec![
                    self.mem.temp[index],
                    self.mem.temp[index+1],
                    self.mem.temp[index+2],
                    self.mem.temp[index+3]]
                ).read_u32::<BigEndian>().unwrap();
                self.stack.write_u32::<BigEndian>(value).unwrap();
            },
            SEGMENT::THIS => {
                let value = Cursor::new(vec![
                    self.mem.this[index],
                    self.mem.this[index+1],
                    self.mem.this[index+2],
                    self.mem.this[index+3]]
                ).read_u32::<BigEndian>().unwrap();
                self.stack.write_u32::<BigEndian>(value).unwrap();
            },
            SEGMENT::THAT => {
                let value = Cursor::new(vec![
                    self.mem.that[index],
                    self.mem.that[index+1],
                    self.mem.that[index+2],
                    self.mem.that[index+3]]
                ).read_u32::<BigEndian>().unwrap();
                self.stack.write_u32::<BigEndian>(value).unwrap();
            },
            SEGMENT::POINTER => {
                let value = Cursor::new(vec![
                    self.mem.pointer[index],
                    self.mem.pointer[index+1],
                    self.mem.pointer[index+2],
                    self.mem.pointer[index+3]]
                ).read_u32::<BigEndian>().unwrap();
                self.stack.write_u32::<BigEndian>(value).unwrap();
            },
            _ => {

            }
        }

        self.sp += 4;
    }

    /// [PUSH, SEGMENT, TYPE, 0,
    /// INDEX, INDEX, INDEX, INDEX]
    pub fn push_segment_i32(&mut self, segment: SEGMENT) {
        let index = self.next_32_bits() as usize;
        match segment {
            SEGMENT::LOCAL => {
                let value = Cursor::new(vec![
                    self.mem.local[index],
                    self.mem.local[index+1],
                    self.mem.local[index+2],
                    self.mem.local[index+3]]
                ).read_i32::<BigEndian>().unwrap();
                self.stack.write_i32::<BigEndian>(value).unwrap();
            },
            SEGMENT::ARGUMENT => {
                let value = Cursor::new(vec![
                    self.mem.argument[index],
                    self.mem.argument[index+1],
                    self.mem.argument[index+2],
                    self.mem.argument[index+3]]
                ).read_i32::<BigEndian>().unwrap();
                self.stack.write_i32::<BigEndian>(value).unwrap();
            },
            SEGMENT::STATIC => {
                let value = Cursor::new(vec![
                    self.mem.sttic[index],
                    self.mem.sttic[index+1],
                    self.mem.sttic[index+2],
                    self.mem.sttic[index+3]]
                ).read_i32::<BigEndian>().unwrap();
                self.stack.write_i32::<BigEndian>(value).unwrap();
            },
            SEGMENT::TEMP => {
                let value = Cursor::new(vec![
                    self.mem.temp[index],
                    self.mem.temp[index+1],
                    self.mem.temp[index+2],
                    self.mem.temp[index+3]]
                ).read_i32::<BigEndian>().unwrap();
                self.stack.write_i32::<BigEndian>(value).unwrap();
            },
            SEGMENT::THIS => {
                let value = Cursor::new(vec![
                    self.mem.this[index],
                    self.mem.this[index+1],
                    self.mem.this[index+2],
                    self.mem.this[index+3]]
                ).read_i32::<BigEndian>().unwrap();
                self.stack.write_i32::<BigEndian>(value).unwrap();
            },
            SEGMENT::THAT => {
                let value = Cursor::new(vec![
                    self.mem.that[index],
                    self.mem.that[index+1],
                    self.mem.that[index+2],
                    self.mem.that[index+3]]
                ).read_i32::<BigEndian>().unwrap();
                self.stack.write_i32::<BigEndian>(value).unwrap();
            },
            SEGMENT::POINTER => {
                let value = Cursor::new(vec![
                    self.mem.pointer[index],
                    self.mem.pointer[index+1],
                    self.mem.pointer[index+2],
                    self.mem.pointer[index+3]]
                ).read_i32::<BigEndian>().unwrap();
                self.stack.write_i32::<BigEndian>(value).unwrap();
            },
            _ => {

            }
        }

        self.sp += 4;
    }

    /// [PUSH, SEGMENT, TYPE, 0,
    /// INDEX, INDEX, INDEX, INDEX]
    pub fn push_segment_u64(&mut self, segment: SEGMENT) {
        let index = self.next_32_bits() as usize;
        match segment {
            SEGMENT::LOCAL => {
                let value = Cursor::new(vec![
                    self.mem.local[index],
                    self.mem.local[index+1],
                    self.mem.local[index+2],
                    self.mem.local[index+3],
                    self.mem.local[index+4],
                    self.mem.local[index+5],
                    self.mem.local[index+6],
                    self.mem.local[index+7]]
                ).read_u64::<BigEndian>().unwrap();
                self.stack.write_u64::<BigEndian>(value).unwrap();
            },
            SEGMENT::ARGUMENT => {
                let value = Cursor::new(vec![
                    self.mem.argument[index],
                    self.mem.argument[index+1],
                    self.mem.argument[index+2],
                    self.mem.argument[index+3],
                    self.mem.argument[index+4],
                    self.mem.argument[index+5],
                    self.mem.argument[index+6],
                    self.mem.argument[index+7]]
                ).read_u64::<BigEndian>().unwrap();
                self.stack.write_u64::<BigEndian>(value).unwrap();
            },
            SEGMENT::STATIC => {
                let value = Cursor::new(vec![
                    self.mem.sttic[index],
                    self.mem.sttic[index+1],
                    self.mem.sttic[index+2],
                    self.mem.sttic[index+3],
                    self.mem.sttic[index+4],
                    self.mem.sttic[index+5],
                    self.mem.sttic[index+6],
                    self.mem.sttic[index+7]]
                ).read_u64::<BigEndian>().unwrap();
                self.stack.write_u64::<BigEndian>(value).unwrap();
            },
            SEGMENT::TEMP => {
                let value = Cursor::new(vec![
                    self.mem.temp[index],
                    self.mem.temp[index+1],
                    self.mem.temp[index+2],
                    self.mem.temp[index+3],
                    self.mem.temp[index+4],
                    self.mem.temp[index+5],
                    self.mem.temp[index+6],
                    self.mem.temp[index+7]]
                ).read_u64::<BigEndian>().unwrap();
                self.stack.write_u64::<BigEndian>(value).unwrap();
            },
            SEGMENT::THIS => {
                let value = Cursor::new(vec![
                    self.mem.this[index],
                    self.mem.this[index+1],
                    self.mem.this[index+2],
                    self.mem.this[index+3],
                    self.mem.this[index+4],
                    self.mem.this[index+5],
                    self.mem.this[index+6],
                    self.mem.this[index+7]]
                ).read_u64::<BigEndian>().unwrap();
                self.stack.write_u64::<BigEndian>(value).unwrap();
            },
            SEGMENT::THAT => {
                let value = Cursor::new(vec![
                    self.mem.that[index],
                    self.mem.that[index+1],
                    self.mem.that[index+2],
                    self.mem.that[index+3],
                    self.mem.that[index+4],
                    self.mem.that[index+5],
                    self.mem.that[index+6],
                    self.mem.that[index+7]]
                ).read_u64::<BigEndian>().unwrap();
                self.stack.write_u64::<BigEndian>(value).unwrap();
            },
            SEGMENT::POINTER => {
                let value = Cursor::new(vec![
                    self.mem.pointer[index],
                    self.mem.pointer[index+1],
                    self.mem.pointer[index+2],
                    self.mem.pointer[index+3],
                    self.mem.pointer[index+4],
                    self.mem.pointer[index+5],
                    self.mem.pointer[index+6],
                    self.mem.pointer[index+7]]
                ).read_u64::<BigEndian>().unwrap();
                self.stack.write_u64::<BigEndian>(value).unwrap();
            },
            _ => {

            }
        }

        self.sp += 8;
    }

    /// [PUSH, SEGMENT, TYPE, 0,
    /// INDEX, INDEX, INDEX, INDEX]
    pub fn push_segment_i64(&mut self, segment: SEGMENT) {
        let index = self.next_32_bits() as usize;
        match segment {
            SEGMENT::LOCAL => {
                let value = Cursor::new(vec![
                    self.mem.local[index],
                    self.mem.local[index+1],
                    self.mem.local[index+2],
                    self.mem.local[index+3],
                    self.mem.local[index+4],
                    self.mem.local[index+5],
                    self.mem.local[index+6],
                    self.mem.local[index+7]]
                ).read_i64::<BigEndian>().unwrap();
                self.stack.write_i64::<BigEndian>(value).unwrap();
            },
            SEGMENT::ARGUMENT => {
                let value = Cursor::new(vec![
                    self.mem.argument[index],
                    self.mem.argument[index+1],
                    self.mem.argument[index+2],
                    self.mem.argument[index+3],
                    self.mem.argument[index+4],
                    self.mem.argument[index+5],
                    self.mem.argument[index+6],
                    self.mem.argument[index+7]]
                ).read_i64::<BigEndian>().unwrap();
                self.stack.write_i64::<BigEndian>(value).unwrap();
            },
            SEGMENT::STATIC => {
                let value = Cursor::new(vec![
                    self.mem.sttic[index],
                    self.mem.sttic[index+1],
                    self.mem.sttic[index+2],
                    self.mem.sttic[index+3],
                    self.mem.sttic[index+4],
                    self.mem.sttic[index+5],
                    self.mem.sttic[index+6],
                    self.mem.sttic[index+7]]
                ).read_i64::<BigEndian>().unwrap();
                self.stack.write_i64::<BigEndian>(value).unwrap();
            },
            SEGMENT::TEMP => {
                let value = Cursor::new(vec![
                    self.mem.temp[index],
                    self.mem.temp[index+1],
                    self.mem.temp[index+2],
                    self.mem.temp[index+3],
                    self.mem.temp[index+4],
                    self.mem.temp[index+5],
                    self.mem.temp[index+6],
                    self.mem.temp[index+7]]
                ).read_i64::<BigEndian>().unwrap();
                self.stack.write_i64::<BigEndian>(value).unwrap();
            },
            SEGMENT::THIS => {
                let value = Cursor::new(vec![
                    self.mem.this[index],
                    self.mem.this[index+1],
                    self.mem.this[index+2],
                    self.mem.this[index+3],
                    self.mem.this[index+4],
                    self.mem.this[index+5],
                    self.mem.this[index+6],
                    self.mem.this[index+7]]
                ).read_i64::<BigEndian>().unwrap();
                self.stack.write_i64::<BigEndian>(value).unwrap();
            },
            SEGMENT::THAT => {
                let value = Cursor::new(vec![
                    self.mem.that[index],
                    self.mem.that[index+1],
                    self.mem.that[index+2],
                    self.mem.that[index+3],
                    self.mem.that[index+4],
                    self.mem.that[index+5],
                    self.mem.that[index+6],
                    self.mem.that[index+7]]
                ).read_i64::<BigEndian>().unwrap();
                self.stack.write_i64::<BigEndian>(value).unwrap();
            },
            SEGMENT::POINTER => {
                let value = Cursor::new(vec![
                    self.mem.pointer[index],
                    self.mem.pointer[index+1],
                    self.mem.pointer[index+2],
                    self.mem.pointer[index+3],
                    self.mem.pointer[index+4],
                    self.mem.pointer[index+5],
                    self.mem.pointer[index+6],
                    self.mem.pointer[index+7]]
                ).read_i64::<BigEndian>().unwrap();
                self.stack.write_i64::<BigEndian>(value).unwrap();
            },
            _ => {

            }
        }

        self.sp += 8;
    }

    /// [PUSH, SEGMENT, TYPE, 0,
    /// INDEX, INDEX, INDEX, INDEX]
    pub fn push_segment_f32(&mut self, segment: SEGMENT) {
        let index = self.next_32_bits() as usize;
        match segment {
            SEGMENT::LOCAL => {
                let value = Cursor::new(vec![
                    self.mem.local[index],
                    self.mem.local[index+1],
                    self.mem.local[index+2],
                    self.mem.local[index+3]]
                ).read_f32::<BigEndian>().unwrap();
                self.stack.write_f32::<BigEndian>(value).unwrap();
            },
            SEGMENT::ARGUMENT => {
                let value = Cursor::new(vec![
                    self.mem.argument[index],
                    self.mem.argument[index+1],
                    self.mem.argument[index+2],
                    self.mem.argument[index+3]]
                ).read_f32::<BigEndian>().unwrap();
                self.stack.write_f32::<BigEndian>(value).unwrap();
            },
            SEGMENT::STATIC => {
                let value = Cursor::new(vec![
                    self.mem.sttic[index],
                    self.mem.sttic[index+1],
                    self.mem.sttic[index+2],
                    self.mem.sttic[index+3]]
                ).read_f32::<BigEndian>().unwrap();
                self.stack.write_f32::<BigEndian>(value).unwrap();
            },
            SEGMENT::TEMP => {
                let value = Cursor::new(vec![
                    self.mem.temp[index],
                    self.mem.temp[index+1],
                    self.mem.temp[index+2],
                    self.mem.temp[index+3]]
                ).read_f32::<BigEndian>().unwrap();
                self.stack.write_f32::<BigEndian>(value).unwrap();
            },
            SEGMENT::THIS => {
                let value = Cursor::new(vec![
                    self.mem.this[index],
                    self.mem.this[index+1],
                    self.mem.this[index+2],
                    self.mem.this[index+3]]
                ).read_f32::<BigEndian>().unwrap();
                self.stack.write_f32::<BigEndian>(value).unwrap();
            },
            SEGMENT::THAT => {
                let value = Cursor::new(vec![
                    self.mem.that[index],
                    self.mem.that[index+1],
                    self.mem.that[index+2],
                    self.mem.that[index+3]]
                ).read_f32::<BigEndian>().unwrap();
                self.stack.write_f32::<BigEndian>(value).unwrap();
            },
            SEGMENT::POINTER => {
                let value = Cursor::new(vec![
                    self.mem.pointer[index],
                    self.mem.pointer[index+1],
                    self.mem.pointer[index+2],
                    self.mem.pointer[index+3]]
                ).read_f32::<BigEndian>().unwrap();
                self.stack.write_f32::<BigEndian>(value).unwrap();
            },
            _ => {

            }
        }

        self.sp += 4;
    }

    /// [PUSH, SEGMENT, TYPE, 0,
    /// INDEX, INDEX, INDEX, INDEX]
    pub fn push_segment_f64(&mut self, segment: SEGMENT) {
        let index = self.next_32_bits() as usize;
        match segment {
            SEGMENT::LOCAL => {
                let value = Cursor::new(vec![
                    self.mem.local[index],
                    self.mem.local[index+1],
                    self.mem.local[index+2],
                    self.mem.local[index+3],
                    self.mem.local[index+4],
                    self.mem.local[index+5],
                    self.mem.local[index+6],
                    self.mem.local[index+7]]
                ).read_f64::<BigEndian>().unwrap();
                self.stack.write_f64::<BigEndian>(value).unwrap();
            },
            SEGMENT::ARGUMENT => {
                let value = Cursor::new(vec![
                    self.mem.argument[index],
                    self.mem.argument[index+1],
                    self.mem.argument[index+2],
                    self.mem.argument[index+3],
                    self.mem.argument[index+4],
                    self.mem.argument[index+5],
                    self.mem.argument[index+6],
                    self.mem.argument[index+7]]
                ).read_f64::<BigEndian>().unwrap();
                self.stack.write_f64::<BigEndian>(value).unwrap();
            },
            SEGMENT::STATIC => {
                let value = Cursor::new(vec![
                    self.mem.sttic[index],
                    self.mem.sttic[index+1],
                    self.mem.sttic[index+2],
                    self.mem.sttic[index+3],
                    self.mem.sttic[index+4],
                    self.mem.sttic[index+5],
                    self.mem.sttic[index+6],
                    self.mem.sttic[index+7]]
                ).read_f64::<BigEndian>().unwrap();
                self.stack.write_f64::<BigEndian>(value).unwrap();
            },
            SEGMENT::TEMP => {
                let value = Cursor::new(vec![
                    self.mem.temp[index],
                    self.mem.temp[index+1],
                    self.mem.temp[index+2],
                    self.mem.temp[index+3],
                    self.mem.temp[index+4],
                    self.mem.temp[index+5],
                    self.mem.temp[index+6],
                    self.mem.temp[index+7]]
                ).read_f64::<BigEndian>().unwrap();
                self.stack.write_f64::<BigEndian>(value).unwrap();
            },
            SEGMENT::THIS => {
                let value = Cursor::new(vec![
                    self.mem.this[index],
                    self.mem.this[index+1],
                    self.mem.this[index+2],
                    self.mem.this[index+3],
                    self.mem.this[index+4],
                    self.mem.this[index+5],
                    self.mem.this[index+6],
                    self.mem.this[index+7]]
                ).read_f64::<BigEndian>().unwrap();
                self.stack.write_f64::<BigEndian>(value).unwrap();
            },
            SEGMENT::THAT => {
                let value = Cursor::new(vec![
                    self.mem.that[index],
                    self.mem.that[index+1],
                    self.mem.that[index+2],
                    self.mem.that[index+3],
                    self.mem.that[index+4],
                    self.mem.that[index+5],
                    self.mem.that[index+6],
                    self.mem.that[index+7]]
                ).read_f64::<BigEndian>().unwrap();
                self.stack.write_f64::<BigEndian>(value).unwrap();
            },
            SEGMENT::POINTER => {
                let value = Cursor::new(vec![
                    self.mem.pointer[index],
                    self.mem.pointer[index+1],
                    self.mem.pointer[index+2],
                    self.mem.pointer[index+3],
                    self.mem.pointer[index+4],
                    self.mem.pointer[index+5],
                    self.mem.pointer[index+6],
                    self.mem.pointer[index+7]]
                ).read_f64::<BigEndian>().unwrap();
                self.stack.write_f64::<BigEndian>(value).unwrap();
            },
            _ => {

            }
        }

        self.sp += 8;
    }

    fn pop_segment_u8(&mut self, segment: SEGMENT) -> Option<u8> {
        let index = self.next_32_bits() as usize;
        if let Some(value) = self.stack.pop() {
            self.mem.local[index as usize] = value;
            self.sp -= 1;
            None
        } else {
            return Some(1);
        }
    }

    fn pop_segment_i8(&mut self, segment: SEGMENT) {
        let index = self.next_32_bits() as usize;
        let value = Cursor::new([self.stack.pop().unwrap()]).read_i8().unwrap();
        match segment {
            SEGMENT::LOCAL => self.mem.local.write_i8(value).unwrap(),
            SEGMENT::ARGUMENT => self.mem.argument.write_i8(value).unwrap(),
            SEGMENT::STATIC => self.mem.sttic.write_i8(value).unwrap(),
            SEGMENT::TEMP => self.mem.temp.write_i8(value).unwrap(),
            SEGMENT::THIS => self.mem.this.write_i8(value).unwrap(),
            SEGMENT::THAT => self.mem.that.write_i8(value).unwrap(),
            SEGMENT::POINTER => self.mem.pointer.write_i8(value).unwrap(),
            _ => {}
        }
    }

    fn pop_segment_u16(&mut self, segment: SEGMENT) {
        let index = self.next_32_bits() as usize;
        let value = Cursor::new([self.stack.pop().unwrap(), self.stack.pop().unwrap()]).read_u16::<BigEndian>().unwrap();
        match segment {
            SEGMENT::LOCAL => self.mem.local[index].write_u16::<BigEndian>(value).unwrap(),
            SEGMENT::ARGUMENT => self.mem.argument.write_u16::<BigEndian>(value).unwrap(),
            SEGMENT::STATIC => self.mem.sttic.write_u16::<BigEndian>(value).unwrap(),
            SEGMENT::TEMP => self.mem.temp.write_u16::<BigEndian>(value).unwrap(),
            SEGMENT::THIS => self.mem.this.write_u16::<BigEndian>(value).unwrap(),
            SEGMENT::THAT => self.mem.that.write_u16::<BigEndian>(value).unwrap(),
            SEGMENT::POINTER => self.mem.pointer.write_u16::<BigEndian>(value).unwrap(),
            _ => {}
        }
    }

}

impl PICOVM {
    pub fn read_stack_u8(&mut self, index: usize) -> u8 {
        self.stack[index]
    }

    pub fn read_stack_i8(&mut self, index: usize) -> i8 {
        Cursor::new(vec![self.stack[index]]).read_i8().unwrap()
    }

    pub fn read_stack_u16(&mut self, index: usize) -> u16 {
        let i = index*2;
        Cursor::new(&self.stack[i..i+2]).read_u16::<BigEndian>().unwrap()
    }

    pub fn read_stack_i16(&mut self, index: usize) -> i16 {
        let i = index*2;
        Cursor::new(&self.stack[i..i+2]).read_i16::<BigEndian>().unwrap()
    }

    pub fn read_stack_u32(&mut self, index: usize) -> u32 {
        let i = index*4;
        Cursor::new(&self.stack[i..i+4]).read_u32::<BigEndian>().unwrap()
    }

    pub fn read_stack_i32(&mut self, index: usize) -> i32 {
        let i = index*4;
        Cursor::new(&self.stack[i..i+4]).read_i32::<BigEndian>().unwrap()
    }

    pub fn read_stack_u64(&mut self, index: usize) -> u64 {
        let i = index*8;
        Cursor::new(&self.stack[i..i+8]).read_u64::<BigEndian>().unwrap()
    }

    pub fn read_stack_i64(&mut self, index: usize) -> i64 {
        let i = index*8;
        Cursor::new(&self.stack[i..i+8]).read_i64::<BigEndian>().unwrap()
    }

    pub fn read_stack_f32(&mut self, index: usize) -> f32 {
        let i = index*4;
        Cursor::new(&self.stack[i..i+4]).read_f32::<BigEndian>().unwrap()
    }

    pub fn read_stack_f64(&mut self, index: usize) -> f64 {
        let i = index*8;
        Cursor::new(&self.stack[i..i+8]).read_f64::<BigEndian>().unwrap()
    }

}

#[cfg(test)]
mod tests {
    use super::*;
    /*
    0 => TYPE::ATOM,
    1 => TYPE::U8,
    2 => TYPE::U16,
    3 => TYPE::U32,
    4 => TYPE::U64,
    5 => TYPE::I8,
    6 => TYPE::I16,
    7 => TYPE::I32,
    8 => TYPE::I64,
    9 => TYPE::F32,
    10 => TYPE::F64,
    */
    const PUSH : u8 = 1;
    const LOCAL: u8 = 0;
    const CONSTANT: u8 = 4;

    const U8: u8 = 1;
    const U16: u8 = 2;
    const U32: u8 = 3;
    const U64: u8 = 4;
    const I8: u8 = 5;
    const I16: u8 = 6;
    const I32: u8 = 7;
    const I64: u8 = 8;
    const F32: u8 = 9;
    const F64: u8 = 10;

    #[test]
    fn push_const_u8() {
        let mut vm = PICOVM::new();
        vm.program = vec![PUSH,CONSTANT,U8,0];
        vm.program.write_u8(240).unwrap();
        vm.run_once();
        assert_eq!(240, vm.read_stack_u8(0));
    }

    #[test]
    fn push_const_i8() {
        let mut vm = PICOVM::new();
        vm.program = vec![PUSH,CONSTANT,I8,0];
        vm.program.write_i8(-123).unwrap();
        vm.run_once();
        assert_eq!(-123, vm.read_stack_i8(0));
    }

    #[test]
    fn push_local_i8() {
        let mut vm = PICOVM::new();
        vm.mem.local.write_i8(-123).unwrap();
        vm.mem.local.write_i8(-122).unwrap();
        vm.program = vec![PUSH, LOCAL, I8, 0];
        vm.program.write_u32::<BigEndian>(0).unwrap();
        vm.program.append(&mut vec![PUSH,LOCAL,I8,0]);
        vm.program.write_u32::<BigEndian>(1).unwrap();
        vm.run_once();
        vm.run_once();
        println!("{:?}", vm.stack);
        assert_eq!(-123, vm.read_stack_i8(0));
        assert_eq!(-122, vm.read_stack_i8(1));
    }

    #[test]
    fn push_const_u16() {
        let mut vm = PICOVM::new();
        vm.program = vec![PUSH,CONSTANT,U16,0];
        vm.program.write_u16::<BigEndian>(1234).unwrap();
        vm.run_once();
        assert_eq!(1234, vm.read_stack_u16(0));
    }

    #[test]
    fn push_local_u16() {
        let mut vm = PICOVM::new();
        vm.mem.local.write_u16::<BigEndian>(123).unwrap();
        vm.mem.local.write_u16::<BigEndian>(122).unwrap();
        println!("{:?}", vm.mem.local);
        vm.program = vec![PUSH, LOCAL, U16, 0];
        vm.program.write_u32::<BigEndian>(0).unwrap();
        vm.program.append(&mut vec![PUSH,LOCAL,U16,0]);
        vm.program.write_u32::<BigEndian>(2).unwrap();
        vm.run_once();
        vm.run_once();
        println!("{:?}", vm.stack);
        assert_eq!(123, vm.read_stack_u16(0));
        assert_eq!(122, vm.read_stack_u16(1));
    }

    #[test]
    fn push_const_i16() {
        let mut vm = PICOVM::new();
        vm.program = vec![PUSH,CONSTANT,I16,0];
        vm.program.write_i16::<BigEndian>(-1234).unwrap();
        vm.run_once();
        assert_eq!(-1234, vm.read_stack_i16(0));
    }

    #[test]
    fn push_local_i16() {
        let mut vm = PICOVM::new();
        vm.mem.local.write_i16::<BigEndian>(-123).unwrap();
        vm.mem.local.write_i16::<BigEndian>(-122).unwrap();
        println!("{:?}", vm.mem.local);
        vm.program = vec![PUSH, LOCAL, U16, 0];
        vm.program.write_u32::<BigEndian>(0).unwrap();
        vm.program.append(&mut vec![PUSH,LOCAL,U16,0]);
        vm.program.write_u32::<BigEndian>(2).unwrap();
        vm.run_once();
        vm.run_once();
        println!("{:?}", vm.stack);
        assert_eq!(-123, vm.read_stack_i16(0));
        assert_eq!(-122, vm.read_stack_i16(1));
    }

    #[test]
    fn push_const_u32() {
        let mut vm = PICOVM::new();
        vm.program = vec![PUSH,CONSTANT,U32,0];
        vm.program.write_u32::<BigEndian>(1234).unwrap();
        vm.run_once();
        assert_eq!(1234, vm.read_stack_u32(0));
    }

    #[test]
    fn push_local_u32() {
        let mut vm = PICOVM::new();
        vm.mem.local.write_u32::<BigEndian>(123).unwrap();
        vm.mem.local.write_u32::<BigEndian>(122).unwrap();
        println!("{:?}", vm.mem.local);
        vm.program = vec![PUSH, LOCAL, U32, 0];
        vm.program.write_u32::<BigEndian>(0).unwrap();
        vm.program.append(&mut vec![PUSH,LOCAL,U32,0]);
        vm.program.write_u32::<BigEndian>(4).unwrap();
        vm.run_once();
        vm.run_once();
        println!("{:?}", vm.stack);
        assert_eq!(123, vm.read_stack_u32(0));
        assert_eq!(122, vm.read_stack_u32(1));
    }

    #[test]
    fn push_const_i32() {
        let mut vm = PICOVM::new();
        vm.program = vec![PUSH,CONSTANT,I32,0];
        vm.program.write_i32::<BigEndian>(-1234).unwrap();
        vm.run_once();
        assert_eq!(-1234, vm.read_stack_i32(0));
    }

    #[test]
    fn push_local_i32() {
        let mut vm = PICOVM::new();
        vm.mem.local.write_i32::<BigEndian>(-123).unwrap();
        vm.mem.local.write_i32::<BigEndian>(-122).unwrap();
        println!("{:?}", vm.mem.local);
        vm.program = vec![PUSH, LOCAL, I32, 0];
        vm.program.write_u32::<BigEndian>(0).unwrap();
        vm.program.append(&mut vec![PUSH,LOCAL,I32,0]);
        vm.program.write_u32::<BigEndian>(4).unwrap();
        vm.run_once();
        vm.run_once();
        println!("{:?}", vm.stack);
        assert_eq!(-123, vm.read_stack_i32(0));
        assert_eq!(-122, vm.read_stack_i32(1));
    }

    #[test]
    fn push_const_u64() {
        let mut vm = PICOVM::new();
        vm.program = vec![PUSH,CONSTANT,U64,0];
        vm.program.write_u64::<BigEndian>(1234).unwrap();
        vm.run_once();
        assert_eq!(1234, vm.read_stack_u64(0));
    }

    #[test]
    fn push_local_u64() {
        let mut vm = PICOVM::new();
        vm.mem.local.write_u64::<BigEndian>(123).unwrap();
        vm.mem.local.write_u64::<BigEndian>(122).unwrap();
        println!("{:?}", vm.mem.local);
        vm.program = vec![PUSH, LOCAL, U64, 0];
        vm.program.write_u32::<BigEndian>(0).unwrap();
        vm.program.append(&mut vec![PUSH,LOCAL,U64,0]);
        vm.program.write_u32::<BigEndian>(8).unwrap();
        vm.run_once();
        vm.run_once();
        println!("{:?}", vm.stack);
        assert_eq!(123, vm.read_stack_u64(0));
        assert_eq!(122, vm.read_stack_u64(1));
    }

    #[test]
    fn push_const_i64() {
        let mut vm = PICOVM::new();
        vm.program = vec![PUSH,CONSTANT,I64,0];
        vm.program.write_i64::<BigEndian>(-1234).unwrap();
        vm.run_once();
        assert_eq!(-1234, vm.read_stack_i64(0));
    }

    #[test]
    fn push_local_i64() {
        let mut vm = PICOVM::new();
        vm.mem.local.write_i64::<BigEndian>(-123).unwrap();
        vm.mem.local.write_i64::<BigEndian>(-122).unwrap();
        println!("{:?}", vm.mem.local);
        vm.program = vec![PUSH, LOCAL, I64, 0];
        vm.program.write_u32::<BigEndian>(0).unwrap();
        vm.program.append(&mut vec![PUSH,LOCAL, I64,0]);
        vm.program.write_u32::<BigEndian>(8).unwrap();
        vm.run_once();
        vm.run_once();
        println!("{:?}", vm.stack);
        assert_eq!(-123, vm.read_stack_i64(0));
        assert_eq!(-122, vm.read_stack_i64(1));
    }

    #[test]
    fn push_const_f32() {
        let mut vm = PICOVM::new();
        vm.program = vec![PUSH,CONSTANT,F32,0];
        vm.program.write_f32::<BigEndian>(-1234.0).unwrap();
        vm.run_once();
        assert_eq!(-1234.0, vm.read_stack_f32(0));
    }

    #[test]
    fn push_local_f32() {
        let mut vm = PICOVM::new();
        vm.mem.local.write_f32::<BigEndian>(-123.0).unwrap();
        vm.mem.local.write_f32::<BigEndian>(-122.0).unwrap();
        println!("{:?}", vm.mem.local);
        vm.program = vec![PUSH, LOCAL, F32, 0];
        vm.program.write_u32::<BigEndian>(0).unwrap();
        vm.program.append(&mut vec![PUSH, LOCAL, F32, 0]);
        vm.program.write_u32::<BigEndian>(4).unwrap();
        vm.run_once();
        vm.run_once();
        println!("{:?}", vm.stack);
        assert_eq!(-123.0, vm.read_stack_f32(0));
        assert_eq!(-122.0, vm.read_stack_f32(1));
    }

    #[test]
    fn push_const_f64() {
        let mut vm = PICOVM::new();
        vm.program = vec![PUSH,CONSTANT,F64,0];
        vm.program.write_f64::<BigEndian>(-1234.0).unwrap();
        vm.run_once();
        assert_eq!(-1234.0, vm.read_stack_f64(0));
    }

    #[test]
    fn push_local_f64() {
        let mut vm = PICOVM::new();
        vm.mem.local.write_f64::<BigEndian>(-123.0).unwrap();
        vm.mem.local.write_f64::<BigEndian>(-122.0).unwrap();
        println!("{:?}", vm.mem.local);
        vm.program = vec![PUSH, LOCAL, F64, 0];
        vm.program.write_u32::<BigEndian>(0).unwrap();
        vm.program.append(&mut vec![PUSH, LOCAL, F64, 0]);
        vm.program.write_u32::<BigEndian>(8).unwrap();
        vm.run_once();
        vm.run_once();
        println!("{:?}", vm.stack);
        assert_eq!(-123.0, vm.read_stack_f64(0));
        assert_eq!(-122.0, vm.read_stack_f64(1));
    }

    #[test]
    fn push_3_consts_f64() {
        let mut vm = PICOVM::new();
        vm.program = vec![PUSH,CONSTANT,F64,0];
        vm.program.write_f64::<BigEndian>(-1234.0).unwrap();
        vm.program.append(&mut vec![PUSH,CONSTANT,F64,0]);
        vm.program.write_f64::<BigEndian>(-4321.0).unwrap();
        vm.program.append(&mut vec![PUSH,CONSTANT,F64,0]);
        vm.program.write_f64::<BigEndian>(-87654321.0).unwrap();
        println!("{:?}", vm.program);
        vm.run_once();
        vm.run_once();
        vm.run_once();
        assert_eq!(-1234.0, vm.read_stack_f64(0));
        assert_eq!(-4321.0, vm.read_stack_f64(1));
        assert_eq!(-87654321.0, vm.read_stack_f64(2));
    }

    #[test]
    fn push_2_consts_i32() {
        let mut vm = PICOVM::new();
        vm.program = vec![PUSH,CONSTANT,I32,0];
        vm.program.write_i32::<BigEndian>(-1234).unwrap();
        vm.program.append(&mut vec![PUSH,CONSTANT,I32,0]);
        vm.program.write_i32::<BigEndian>(-4321).unwrap();
        vm.run_once();
        vm.run_once();
        assert_eq!(-1234, vm.read_stack_i32(0));
        assert_eq!(-4321, vm.read_stack_i32(1));
    }


}
