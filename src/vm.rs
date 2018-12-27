use crate::opcode::{OPCODE, SEGMENT, TYPE};
use byteorder::*;

use byteorder::BigEndian;
use std::collections::HashMap;

#[derive(Default, Clone)]
pub struct PICOVM {
    registers: [u64; 32],
    program: Vec<u8>,
    stack: Vec<u8>,
    mem: MEMORY,
    pc: usize,
    sp: usize,
    flags: u8,
    symbol_list: Box<HashMap<String, usize>>,
}

#[derive(Default, Clone)]
pub struct MEMORY {
    local: Box<[u8]>,
    argument: Box<[u8]>,
    this: Box<[u8]>,
    that: Box<[u8]>,
    sttic: Box<[u8]>,
    pointer: Box<[u8]>,
    temp: Box<[u8]>,
}

impl MEMORY {
    pub fn new() -> Self {
        MEMORY {
            local: Box::new([0; 256]),
            argument: Box::new([0; 256]),
            this: Box::new([0; 256]),
            that: Box::new([0; 256]),
            sttic: Box::new([0; 256]),
            pointer: Box::new([0; 256]),
            temp: Box::new([0; 256]),
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
            symbol_list: Box::new(HashMap::new()),
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
                        // let value = self.next_8_bits();
                        // self.stack.push(value);
                        // self.sp += 1;
                        // self.next_8_bits();
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
                                let value = self.next_8_bits();
                                self.stack.write_i8(value as i8).unwrap();
                                self.sp += 1;
                            }
                            TYPE::I16 => {
                                let value = self.next_16_bits();
                                self.stack.write_i16::<BigEndian>(value as i16).unwrap();
                                self.sp += 2;
                            }
                            TYPE::I32 => {
                                let value = self.next_32_bits();
                                self.stack.write_i32::<BigEndian>(value as i32).unwrap();
                                self.sp += 4;
                            }
                            TYPE::I64 => {
                                let value =
                                    i64::from(self.next_8_bytes_be().to_vec().read_i64().unwrap());
                                self.stack.write_i64::<BigEndian>(value).unwrap();
                                self.sp += 8;
                            }
                            TYPE::F32 => {
                                let value = f32::from(self.next_16_bits());
                                self.stack.write_f32::<BigEndian>(value).unwrap();
                            }
                            _ => {
                                return Some(1);
                            }
                        }
                    }
                    SEGMENT::LOCAL => {
                        let index = self.next_8_bits();
                        self.stack.push(self.mem.local[index as usize]);
                        self.sp += 1;
                        self.next_8_bits();
                    }
                    SEGMENT::ARGUMENT => {
                        let index = self.next_8_bits();
                        self.stack.push(self.mem.argument[index as usize]);
                        self.sp += 1;
                        self.next_8_bits();
                    }
                    SEGMENT::THIS => {
                        let index = self.next_8_bits();
                        self.stack.push(self.mem.this[index as usize]);
                        self.sp += 1;
                        self.next_8_bits();
                    }
                    SEGMENT::THAT => {
                        let index = self.next_8_bits();
                        self.stack.push(self.mem.that[index as usize]);
                        self.sp += 1;
                        self.next_8_bits();
                    }
                    SEGMENT::STATIC => {
                        let index = self.next_8_bits();
                        self.stack.push(self.mem.sttic[index as usize]);
                        self.sp += 1;
                        self.next_8_bits();
                    }
                    SEGMENT::POINTER => {
                        let index = self.next_8_bits();
                        self.stack.push(self.mem.pointer[index as usize]);
                        self.sp += 1;
                        self.next_8_bits();
                    }
                    SEGMENT::TEMP => {
                        let index = self.next_8_bits();
                        self.stack.push(self.mem.temp[index as usize]);
                        self.sp += 1;
                        self.next_8_bits();
                    }
                    SEGMENT::IGL => {
                        return Some(1);
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
            _ => {
                return Some(1);
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

    fn next_16_bits(&mut self) -> u16 {
        let result =
            ((u16::from(self.program[self.pc])) << 8) | u16::from(self.program[self.pc + 1]);
        self.pc += 2;
        result
    }

    fn next_2_bytes_be(&mut self) -> [u8; 2] {
        let res = [self.program[self.pc], self.program[self.pc + 1]];
        self.pc += 2;
        Cursor::new()
    }

    fn next_32_bits(&mut self) -> u32 {
        let result = ((u32::from(self.program[self.pc])) << 24)
            | ((u32::from(self.program[self.pc + 1])) << 16)
            | ((u32::from(self.program[self.pc + 2])) << 8)
            | u32::from(self.program[self.pc + 3]);
        self.pc += 4;
        result
    }

    fn next_4_bytes_be(&mut self) -> [u8; 4] {
        let res = [
            self.program[self.pc],
            self.program[self.pc + 1],
            self.program[self.pc + 2],
            self.program[self.pc + 3],
        ];
        self.pc += 4;
        res
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

    fn next_8_bytes_be(&mut self) -> [u8; 8] {
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
        res
    }
}
