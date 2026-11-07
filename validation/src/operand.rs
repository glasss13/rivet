use crate::register::{Register8, Register16, Register32, Register64};
use serde::{Deserialize, Serialize};
use std::fmt;
use strum::{Display, VariantArray};

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq, VariantArray, Display)]
#[serde(rename_all = "lowercase")]
#[strum(serialize_all = "UPPERCASE")]
pub enum Width {
    Byte = 8,
    Word = 16,
    Dword = 32,
    Qword = 64,
}
impl Width {
    pub fn bits(self) -> u32 {
        self as u32
    }
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq, VariantArray)]
#[serde(rename_all = "lowercase")]
pub enum Scale {
    One = 1,
    Two = 2,
    Four = 4,
    Eight = 8,
}
impl Scale {
    pub fn value(self) -> u64 {
        self as u64
    }
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct Address {
    pub base: Option<Register64>,
    pub index: Option<Register64>,
    pub scale: Scale,
    pub displacement: i32,
}
impl fmt::Display for Address {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "[")?;
        if let Some(base) = self.base {
            write!(formatter, "{base}")?;
        }
        if let Some(index) = self.index {
            let separator = if self.base.is_some() { "+" } else { "" };
            write!(formatter, "{separator}{index}*{}", self.scale.value())?;
        }
        if self.base.is_none() && self.index.is_none() {
            write!(formatter, "{}", self.displacement)?;
        } else if self.displacement != 0 {
            write!(formatter, "{:+}", self.displacement)?;
        }
        write!(formatter, "]")
    }
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
impl Operand {
    pub fn register(width: Width, register: Register64) -> Self {
        let index = register as usize;
        match width {
            Width::Byte => Self::Reg8 {
                register: Register8::VARIANTS[index],
            },
            Width::Word => Self::Reg16 {
                register: Register16::VARIANTS[index],
            },
            Width::Dword => Self::Reg32 {
                register: Register32::VARIANTS[index],
            },
            Width::Qword => Self::Reg64 { register },
        }
    }
}
impl fmt::Display for Operand {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Reg8 { register } => write!(formatter, "{register}"),
            Self::Reg16 { register } => write!(formatter, "{register}"),
            Self::Reg32 { register } => write!(formatter, "{register}"),
            Self::Reg64 { register } => write!(formatter, "{register}"),
            Self::Memory { width, address } => write!(formatter, "{width} PTR {address}"),
            Self::Immediate { value } => write!(formatter, "{value}"),
        }
    }
}
