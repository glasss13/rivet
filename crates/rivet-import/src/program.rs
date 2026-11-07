use crate::{
    operand::{Address, Operand},
    register::{Register32, Register64, Xmm},
};
use serde::{Deserialize, Serialize};
use strum::{Display, EnumCount, VariantArray};

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq, VariantArray, Display)]
#[serde(rename_all = "lowercase")]
#[strum(serialize_all = "lowercase")]
pub enum BinaryOp {
    Add,
    Sub,
    Sbb,
    Cmp,
    Test,
    And,
    Or,
    Xor,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq, VariantArray, Display)]
#[serde(rename_all = "lowercase")]
#[strum(serialize_all = "lowercase")]
pub enum ShiftOp {
    Shl,
    Shr,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq, VariantArray, Display)]
#[serde(rename_all = "lowercase")]
#[strum(serialize_all = "lowercase")]
pub enum XmmMove {
    Movups,
    Movdqu,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq, VariantArray, Display)]
#[serde(rename_all = "camelCase")]
pub enum Condition {
    #[strum(serialize = "e")]
    Equal,
    #[strum(serialize = "ne")]
    NotEqual,
    #[strum(serialize = "b")]
    Below,
    #[strum(serialize = "ae")]
    AboveOrEqual,
    #[strum(serialize = "be")]
    BelowOrEqual,
    #[strum(serialize = "a")]
    Above,
    #[strum(serialize = "s")]
    Sign,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq, EnumCount)]
#[serde(rename_all = "lowercase")]
pub enum Operation {
    Binary {
        operation: BinaryOp,
        destination: Operand,
        source: Operand,
    },
    Lea {
        destination: Register64,
        source: Address,
    },
    Movzx {
        destination: Register32,
        source: Operand,
    },
    Movsxd {
        destination: Register64,
        source: Operand,
    },
    Mov {
        destination: Operand,
        source: Operand,
    },
    Jmp {
        target: u64,
    },
    Jcc {
        condition: Condition,
        target: u64,
    },
    Setcc {
        condition: Condition,
        destination: Operand,
    },
    Cmovcc {
        condition: Condition,
        destination: Operand,
        source: Operand,
    },
    Inc {
        destination: Register64,
    },
    Dec {
        destination: Register64,
    },
    Ret,
    Not {
        destination: Operand,
    },
    Imul {
        destination: Operand,
        source: Operand,
        immediate: Option<i128>,
    },
    Shift {
        operation: ShiftOp,
        destination: Operand,
        count: u8,
    },
    #[serde(rename = "loadXmm")]
    LoadXmm {
        operation: XmmMove,
        destination: Xmm,
        source: Address,
    },
    #[serde(rename = "storeXmm")]
    StoreXmm {
        operation: XmmMove,
        destination: Address,
        source: Xmm,
    },
    Movd {
        destination: Xmm,
        source: Register32,
    },
    Pshufd {
        destination: Xmm,
        source: Xmm,
        order: u8,
    },
    Push {
        source: Register64,
    },
    Pop {
        destination: Register64,
    },
}
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct Instruction {
    pub address: u64,
    pub length: u64,
    pub op: Operation,
}
