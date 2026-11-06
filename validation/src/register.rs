use serde::{Deserialize, Serialize};
use strum::{Display, VariantArray};

// Order matches the register-value arrays and Lean's registerOrder.
#[derive(Clone, Copy, Debug, Serialize, Deserialize, Display, VariantArray, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
#[strum(serialize_all = "lowercase")]
pub enum Register64 {
    Rax,
    Rbx,
    Rcx,
    Rdx,
    Rsi,
    Rdi,
    Rbp,
    Rsp,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, Display, VariantArray, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
#[strum(serialize_all = "lowercase")]
pub enum Register32 {
    Eax,
    Edx,
}
