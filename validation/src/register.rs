use nix::libc;
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
    Ebx,
    Ecx,
    Edx,
    Esi,
    Edi,
    Ebp,
    Esp,
    R8d,
    R9d,
    R10d,
    R11d,
    R12d,
    R13d,
    R14d,
    R15d,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, Display, VariantArray, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
#[strum(serialize_all = "lowercase")]
pub enum Register8 {
    Al,
    Bl,
    Cl,
    Dl,
    Sil,
    Dil,
    Bpl,
    Spl,
    R8b,
    R9b,
    R10b,
    R11b,
    R12b,
    R13b,
    R14b,
    R15b,
}

pub(crate) fn register_values(registers: &libc::user_regs_struct) -> [u64; 16] {
    [
        registers.rax,
        registers.rbx,
        registers.rcx,
        registers.rdx,
        registers.rsi,
        registers.rdi,
        registers.rbp,
        registers.rsp,
        registers.r8,
        registers.r9,
        registers.r10,
        registers.r11,
        registers.r12,
        registers.r13,
        registers.r14,
        registers.r15,
    ]
}

pub(crate) fn set_registers(registers: &mut libc::user_regs_struct, values: [u64; 16]) {
    [
        registers.rax,
        registers.rbx,
        registers.rcx,
        registers.rdx,
        registers.rsi,
        registers.rdi,
        registers.rbp,
        registers.rsp,
        registers.r8,
        registers.r9,
        registers.r10,
        registers.r11,
        registers.r12,
        registers.r13,
        registers.r14,
        registers.r15,
    ] = values;
}
