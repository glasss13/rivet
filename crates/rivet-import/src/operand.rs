use crate::register::{Register8, Register16, Register32, Register64};
use serde::Serialize;

#[derive(Clone, Copy, Debug, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Width {
    Byte,
    Word,
    Dword,
    Qword,
}
#[derive(Clone, Copy, Debug, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Scale {
    One,
    Two,
    Four,
    Eight,
}
#[derive(Clone, Copy, Debug, Serialize)]
pub struct Address {
    pub base: Option<Register64>,
    pub index: Option<Register64>,
    pub scale: Scale,
    pub displacement: i64,
}
#[derive(Clone, Copy, Debug, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Operand {
    Reg8 { register: Register8 },
    Reg16 { register: Register16 },
    Reg32 { register: Register32 },
    Reg64 { register: Register64 },
    Memory { width: Width, address: Address },
    Immediate { value: i128 },
}
