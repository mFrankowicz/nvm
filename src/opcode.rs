/// byte format:
/// [OPCODE, SEGMENT, TYPE, FREE,
/// [u8, u8, u8, u8, ...]

#[derive(PartialEq, Clone, Debug)]
pub enum OPCODE {
    HLT,
    PUSH(SEGMENT),
    POP(SEGMENT),
    ADD,
    SUB,
    MUL,
    DIV,
    MOD,
    EQ,
    NEQ,
    LT,
    GT,
    LTE,
    GTE,
    AND,
    OR,
    NOT,
    XOR,
    IGL,
}

impl From<OPCODE> for (u8, u8) {
    fn from(v: OPCODE) -> (u8, u8) {
        match v {
            OPCODE::HLT => (0, 100),
            OPCODE::PUSH(seg) => (1, u8::from(seg)),
            OPCODE::POP(seg) => (2, u8::from(seg)),
            OPCODE::ADD => (3, 100),
            OPCODE::SUB => (4, 100),
            OPCODE::MUL => (5, 100),
            OPCODE::DIV => (6, 100),
            OPCODE::MOD => (7, 100),
            OPCODE::EQ => (8, 100),
            OPCODE::NEQ => (9, 100),
            OPCODE::LT => (10, 100),
            OPCODE::GT => (11, 100),
            OPCODE::LTE => (12, 100),
            OPCODE::GTE => (13, 100),
            OPCODE::AND => (14, 100),
            OPCODE::OR => (15, 100),
            OPCODE::NOT => (16, 100),
            OPCODE::XOR => (17, 100),
            OPCODE::IGL => (100, 100),
        }
    }
}

impl From<(u8, u8)> for OPCODE {
    fn from(v: (u8, u8)) -> OPCODE {
        match v {
            (0, _) => OPCODE::HLT,
            (1, seg) => OPCODE::PUSH(SEGMENT::from(seg)),
            (2, seg) => OPCODE::POP(SEGMENT::from(seg)),
            (3, _) => OPCODE::ADD,
            (4, _) => OPCODE::SUB,
            (5, _) => OPCODE::MUL,
            (6, _) => OPCODE::DIV,
            (7, _) => OPCODE::MOD,
            (8, _) => OPCODE::EQ,
            (9, _) => OPCODE::NEQ,
            (10, _) => OPCODE::LT,
            (11, _) => OPCODE::GT,
            (12, _) => OPCODE::LTE,
            (13, _) => OPCODE::GTE,
            (14, _) => OPCODE::AND,
            (15, _) => OPCODE::OR,
            (16, _) => OPCODE::NOT,
            (17, _) => OPCODE::XOR,
            (_, _) => OPCODE::IGL,
        }
    }
}

#[derive(PartialEq, Clone, Copy, Debug)]
pub enum SEGMENT {
    LOCAL,
    ARGUMENT,
    THIS,
    THAT,
    CONSTANT,
    STATIC,
    POINTER,
    TEMP,
    IGL,
}

impl From<u8> for SEGMENT {
    fn from(v: u8) -> SEGMENT {
        match v {
            0 => SEGMENT::LOCAL,
            1 => SEGMENT::ARGUMENT,
            2 => SEGMENT::THIS,
            3 => SEGMENT::THAT,
            4 => SEGMENT::CONSTANT,
            5 => SEGMENT::STATIC,
            6 => SEGMENT::POINTER,
            7 => SEGMENT::TEMP,
            _ => SEGMENT::IGL,
        }
    }
}

impl From<SEGMENT> for u8 {
    fn from(v: SEGMENT) -> u8 {
        match v {
            SEGMENT::LOCAL => 0,
            SEGMENT::ARGUMENT => 1,
            SEGMENT::THIS => 2,
            SEGMENT::THAT => 3,
            SEGMENT::CONSTANT => 4,
            SEGMENT::STATIC => 5,
            SEGMENT::POINTER => 6,
            SEGMENT::TEMP => 7,
            SEGMENT::IGL => 100,
        }
    }
}

#[derive(PartialEq, Clone, Copy, Debug)]
pub enum TYPE {
    ATOM,
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
    F32,
    F64,
    STRING,
    LIST,
    LABEL,
    IGL,
}

impl From<TYPE> for u8 {
    fn from(v: TYPE) -> u8 {
        match v {
            TYPE::ATOM => 0,
            TYPE::U8 => 1,
            TYPE::U16 => 2,
            TYPE::U32 => 3,
            TYPE::U64 => 4,
            TYPE::I8 => 5,
            TYPE::I16 => 6,
            TYPE::I32 => 7,
            TYPE::I64 => 8,
            TYPE::F32 => 9,
            TYPE::F64 => 10,
            TYPE::STRING => 11,
            TYPE::LIST => 12,
            TYPE::LABEL => 13,
            TYPE::IGL => 100,
        }
    }
}

impl From<u8> for TYPE {
    fn from(v: u8) -> TYPE {
        match v {
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
            11 => TYPE::STRING,
            12 => TYPE::LIST,
            13 => TYPE::LABEL,
            _ => TYPE::IGL,
        }
    }
}
