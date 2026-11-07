use crate::register::{Register8, Register16, Register32, Register64};
use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum Width {
    Byte = 8,
    Word = 16,
    Dword = 32,
    Qword = 64,
}
#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum Scale {
    One = 1,
    Two = 2,
    Four = 4,
    Eight = 8,
}
#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct Address {
    pub base: Option<Register64>,
    pub index: Option<Register64>,
    pub scale: Scale,
    pub displacement: i64,
}
#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum Operand {
    Reg8 { register: Register8 },
    Reg16 { register: Register16 },
    Reg32 { register: Register32 },
    Reg64 { register: Register64 },
    Memory { width: Width, address: Address },
    Immediate { value: i128 },
}
