use serde::{Deserialize, Serialize};
use strum::{Display, EnumString, VariantArray};

// Order matches the register-value arrays and Lean's registerOrder.
#[derive(
    Clone, Copy, Debug, Serialize, Deserialize, Display, EnumString, VariantArray, PartialEq, Eq,
)]
#[serde(rename_all = "lowercase")]
#[strum(serialize_all = "lowercase", ascii_case_insensitive)]
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

#[derive(
    Clone, Copy, Debug, Serialize, Deserialize, Display, EnumString, VariantArray, PartialEq, Eq,
)]
#[serde(rename_all = "lowercase")]
#[strum(serialize_all = "lowercase", ascii_case_insensitive)]
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

#[derive(
    Clone, Copy, Debug, Serialize, Deserialize, Display, EnumString, VariantArray, PartialEq, Eq,
)]
#[serde(rename_all = "lowercase")]
#[strum(serialize_all = "lowercase", ascii_case_insensitive)]
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

#[derive(
    Clone, Copy, Debug, Serialize, Deserialize, Display, EnumString, VariantArray, PartialEq, Eq,
)]
#[serde(rename_all = "lowercase")]
#[strum(serialize_all = "lowercase", ascii_case_insensitive)]
pub enum Register8 {
    Al,
    Bl,
    Cl,
    Dl,
    Sil,
    Dil,
    Bpl,
    Spl,
    #[strum(serialize = "r8b", serialize = "r8l", to_string = "r8b")]
    R8l,
    #[strum(serialize = "r9b", serialize = "r9l", to_string = "r9b")]
    R9l,
    #[strum(serialize = "r10b", serialize = "r10l", to_string = "r10b")]
    R10l,
    #[strum(serialize = "r11b", serialize = "r11l", to_string = "r11b")]
    R11l,
    #[strum(serialize = "r12b", serialize = "r12l", to_string = "r12b")]
    R12l,
    #[strum(serialize = "r13b", serialize = "r13l", to_string = "r13b")]
    R13l,
    #[strum(serialize = "r14b", serialize = "r14l", to_string = "r14b")]
    R14l,
    #[strum(serialize = "r15b", serialize = "r15l", to_string = "r15b")]
    R15l,
}

#[derive(
    Clone, Copy, Debug, Serialize, Deserialize, Display, EnumString, VariantArray, PartialEq, Eq,
)]
#[serde(rename_all = "lowercase")]
#[strum(serialize_all = "lowercase", ascii_case_insensitive)]
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
