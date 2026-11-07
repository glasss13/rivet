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
pub enum Register16 {
    Ax,
    Bx,
    Cx,
    Dx,
    Si,
    Di,
    Bp,
    Sp,
    R8w,
    R9w,
    R10w,
    R11w,
    R12w,
    R13w,
    R14w,
    R15w,
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

#[derive(Clone, Copy, Debug, Serialize, Deserialize, Display, VariantArray, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
#[strum(serialize_all = "lowercase")]
pub enum Xmm {
    Xmm0,
    Xmm1,
    Xmm2,
    Xmm3,
    Xmm4,
    Xmm5,
    Xmm6,
    Xmm7,
    Xmm8,
    Xmm9,
    Xmm10,
    Xmm11,
    Xmm12,
    Xmm13,
    Xmm14,
    Xmm15,
}

// Four little-endian 32-bit words per XMM register, matching Linux's register set.
pub(crate) fn xmm_values(registers: &libc::user_fpregs_struct) -> [[u32; 4]; 16] {
    registers.xmm_space.as_chunks::<4>().0.try_into().unwrap()
}

pub(crate) fn set_xmm_registers(registers: &mut libc::user_fpregs_struct, values: [[u32; 4]; 16]) {
    registers.xmm_space.copy_from_slice(values.as_flattened());
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
