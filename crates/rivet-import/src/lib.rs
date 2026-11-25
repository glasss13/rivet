//! Decode machine-code bytes into Rivet instructions. No ELF or process setup is required.
pub mod operand;
pub mod program;
pub mod register;
use anyhow::{Context, Result, bail, ensure};
use iced_x86::{
    Code, ConditionCode, Decoder, DecoderOptions, EncodingKind, Instruction as Decoded, Mnemonic,
    OpKind, Register,
};
use operand::{Address, Operand, Scale, Width};
pub use program::Instruction;
use program::{BinaryOp, Condition, Operation, ShiftOp, XmmMove};
use std::str::FromStr;

/// Decode a contiguous code range. Targets may lie in other ranges of the program.
pub fn decode(bytes: &[u8], base: u64) -> Result<Vec<Instruction>> {
    ensure!(!bytes.is_empty(), "empty code range");
    base.checked_add(bytes.len() as u64)
        .context("code address overflow")?;
    let mut program = Vec::new();
    for instruction in Decoder::with_ip(64, bytes, base, DecoderOptions::NONE) {
        let offset = (instruction.ip() - base) as usize;
        program.push(translate(&instruction, &bytes[offset..])?);
    }
    Ok(program)
}

/// Decode only the instruction starting at `address`, within the supplied file bytes.
pub fn decode_one(bytes: &[u8], address: u64) -> Result<Instruction> {
    ensure!(!bytes.is_empty(), "at {address:#x}: empty code range");
    let instruction = Decoder::with_ip(64, bytes, address, DecoderOptions::NONE).decode();
    translate(&instruction, bytes)
}

fn translate(instruction: &Decoded, bytes: &[u8]) -> Result<Instruction> {
    let op = operation(instruction, &bytes[..instruction.len()])
        .with_context(|| format!("at {:#x}: {instruction}", instruction.ip()))?;
    Ok(Instruction {
        address: instruction.ip(),
        length: instruction.len() as u64,
        op,
    })
}

fn register<T: FromStr>(register: Register) -> Result<T> {
    format!("{register:?}")
        .parse()
        .map_err(|_| anyhow::anyhow!("unsupported register {register:?}"))
}

fn condition(instruction: &Decoded) -> Result<Condition> {
    Ok(match instruction.condition_code() {
        ConditionCode::e => Condition::Equal,
        ConditionCode::ne => Condition::NotEqual,
        ConditionCode::b => Condition::Below,
        ConditionCode::ae => Condition::AboveOrEqual,
        ConditionCode::be => Condition::BelowOrEqual,
        ConditionCode::a => Condition::Above,
        ConditionCode::s => Condition::Sign,
        ConditionCode::l => Condition::Less,
        ConditionCode::ge => Condition::GreaterOrEqual,
        ConditionCode::le => Condition::LessOrEqual,
        ConditionCode::g => Condition::Greater,
        other => bail!("unsupported condition {other:?}"),
    })
}

fn address(instruction: &Decoded) -> Result<Address> {
    if instruction.is_ip_rel_memory_operand() {
        // iced resolves the displacement against the end of the instruction.
        // Rivet evaluates the signed displacement modulo 2^64.
        return Ok(Address {
            base: None,
            index: None,
            scale: Scale::One,
            displacement: instruction.ip_rel_memory_address() as i64,
        });
    }
    let optional = |value| {
        if value == Register::None {
            Ok(None)
        } else {
            register(value).map(Some)
        }
    };
    Ok(Address {
        base: optional(instruction.memory_base())?,
        index: optional(instruction.memory_index())?,
        scale: match instruction.memory_index_scale() {
            1 => Scale::One,
            2 => Scale::Two,
            4 => Scale::Four,
            8 => Scale::Eight,
            _ => unreachable!(),
        },
        displacement: instruction.memory_displacement64() as i64,
    })
}

fn operand(instruction: &Decoded, index: u32) -> Result<Operand> {
    Ok(match instruction.op_kind(index) {
        OpKind::Register => {
            let value = instruction.op_register(index);
            match value.size() {
                1 => Operand::Reg8 {
                    register: register(value)?,
                },
                2 => Operand::Reg16 {
                    register: register(value)?,
                },
                4 => Operand::Reg32 {
                    register: register(value)?,
                },
                8 => Operand::Reg64 {
                    register: register(value)?,
                },
                _ => bail!("unsupported scalar register {value:?}"),
            }
        }
        OpKind::Memory => Operand::Memory {
            width: match instruction.memory_size().size() {
                1 => Width::Byte,
                2 => Width::Word,
                4 => Width::Dword,
                8 => Width::Qword,
                _ => bail!("unsupported memory width"),
            },
            address: address(instruction)?,
        },
        OpKind::Immediate8 | OpKind::Immediate16 | OpKind::Immediate32 | OpKind::Immediate64 => {
            Operand::Immediate {
                value: instruction.immediate(index) as i128,
            }
        }
        OpKind::Immediate8to16
        | OpKind::Immediate8to32
        | OpKind::Immediate8to64
        | OpKind::Immediate32to64 => Operand::Immediate {
            value: instruction.immediate(index) as i64 as i128,
        },
        kind => bail!("unsupported operand {kind:?}"),
    })
}

fn operation(instruction: &Decoded, bytes: &[u8]) -> Result<Operation> {
    use Mnemonic::*;
    ensure!(!instruction.is_invalid(), "invalid or truncated encoding");
    ensure!(
        instruction.encoding() == EncodingKind::Legacy
            && !instruction.has_lock_prefix()
            && !instruction.has_rep_prefix()
            && !instruction.has_repne_prefix(),
        "unsupported encoding or prefix"
    );
    // NOP's apparent operand is not accessed; segment/address-size prefixes
    // used for padding do not affect its behavior.
    if instruction.mnemonic() == Nop {
        return Ok(Operation::Nop);
    }
    ensure!(
        !instruction.has_segment_prefix(),
        "segment overrides are not supported"
    );
    ensure!(
        !bytes
            .iter()
            .take_while(|&&b| matches!(
                b,
                0x40..=0x4f
                    | 0x66
                    | 0x67
                    | 0xf0
                    | 0xf2
                    | 0xf3
                    | 0x26
                    | 0x2e
                    | 0x36
                    | 0x3e
                    | 0x64
                    | 0x65
            ))
            .any(|&b| b == 0x67),
        "address-size overrides are not supported"
    );

    let first = || operand(instruction, 0);
    let second = || operand(instruction, 1);
    Ok(match instruction.mnemonic() {
        Add | Sub | Sbb | Cmp | Test | And | Or | Xor => Operation::Binary {
            operation: match instruction.mnemonic() {
                Add => BinaryOp::Add,
                Sub => BinaryOp::Sub,
                Sbb => BinaryOp::Sbb,
                Cmp => BinaryOp::Cmp,
                Test => BinaryOp::Test,
                And => BinaryOp::And,
                Or => BinaryOp::Or,
                Xor => BinaryOp::Xor,
                _ => unreachable!(),
            },
            destination: first()?,
            source: second()?,
        },
        Mov => Operation::Mov {
            destination: first()?,
            source: second()?,
        },
        Not => Operation::Not {
            destination: first()?,
        },
        Lea => Operation::Lea {
            destination: first()?,
            source: address(instruction)?,
        },
        Movzx => Operation::Movzx {
            destination: register(instruction.op0_register())?,
            source: second()?,
        },
        Movsxd => Operation::Movsxd {
            destination: register(instruction.op0_register())?,
            source: second()?,
        },
        Inc => Operation::Inc {
            destination: first()?,
        },
        Dec => Operation::Dec {
            destination: first()?,
        },
        Push => Operation::Push {
            source: register(instruction.op0_register())?,
        },
        Pop => Operation::Pop {
            destination: register(instruction.op0_register())?,
        },
        Shl | Shr => {
            ensure!(
                instruction.op0_kind() == OpKind::Register
                    && (instruction.op0_register().is_gpr32()
                        || instruction.op0_register().is_gpr64()
                        || (instruction.op0_register().is_gpr8()
                            && instruction.immediate8() % 32 < 8))
                    && instruction.op1_kind() == OpKind::Immediate8,
                "shifts require a 32/64-bit register, or an 8-bit one and a masked count below 8, \
                 and an immediate count"
            );
            Operation::Shift {
                operation: if instruction.mnemonic() == Shl {
                    ShiftOp::Shl
                } else {
                    ShiftOp::Shr
                },
                destination: first()?,
                count: instruction.immediate8(),
            }
        }
        Imul => {
            ensure!(
                instruction.op_count() >= 2,
                "one-operand IMUL is not supported"
            );
            Operation::Imul {
                destination: first()?,
                source: second()?,
                immediate: if instruction.op_count() == 3 {
                    Some(instruction.immediate(2) as i64 as i128)
                } else {
                    None
                },
            }
        }
        Mul => {
            ensure!(
                instruction.code() == Code::Mul_rm64 && instruction.op0_kind() == OpKind::Register,
                "MUL requires a 64-bit register source"
            );
            Operation::Mul {
                source: register(instruction.op0_register())?,
            }
        }
        Tzcnt => Operation::Tzcnt {
            destination: first()?,
            source: second()?,
        },
        Sete | Setne | Setb | Setae | Setbe | Seta | Sets | Setl | Setge | Setle | Setg => {
            Operation::Setcc {
                condition: condition(instruction)?,
                destination: first()?,
            }
        }
        Cmove | Cmovne | Cmovb | Cmovae | Cmovbe | Cmova | Cmovs | Cmovl | Cmovge | Cmovle
        | Cmovg => Operation::Cmovcc {
            condition: condition(instruction)?,
            destination: first()?,
            source: second()?,
        },
        Jmp | Je | Jne | Jb | Jae | Jbe | Ja | Js | Jl | Jge | Jle | Jg => {
            ensure!(
                instruction.op0_kind() == OpKind::NearBranch64,
                "only direct 64-bit-mode jumps are supported"
            );
            let target = instruction.near_branch64();
            if instruction.mnemonic() == Jmp {
                Operation::Jmp { target }
            } else {
                Operation::Jcc {
                    condition: condition(instruction)?,
                    target,
                }
            }
        }
        Movd => {
            ensure!(
                instruction.code() == Code::Movd_xmm_rm32
                    && instruction.op1_kind() == OpKind::Register,
                "MOVD requires an XMM destination and a 32-bit register source"
            );
            Operation::Movd {
                destination: register(instruction.op0_register())?,
                source: register(instruction.op1_register())?,
            }
        }
        Pshufd => {
            ensure!(
                instruction.code() == Code::Pshufd_xmm_xmmm128_imm8
                    && instruction.op1_kind() == OpKind::Register,
                "PSHUFD requires register operands"
            );
            Operation::Pshufd {
                destination: register(instruction.op0_register())?,
                source: register(instruction.op1_register())?,
                order: instruction.immediate8(),
            }
        }
        Movups | Movdqu => {
            let operation = if instruction.mnemonic() == Movups {
                XmmMove::Movups
            } else {
                XmmMove::Movdqu
            };
            match (instruction.op0_kind(), instruction.op1_kind()) {
                (OpKind::Register, OpKind::Memory) => Operation::LoadXmm {
                    operation,
                    destination: register(instruction.op0_register())?,
                    source: address(instruction)?,
                },
                (OpKind::Memory, OpKind::Register) => Operation::StoreXmm {
                    operation,
                    destination: address(instruction)?,
                    source: register(instruction.op1_register())?,
                },
                _ => bail!("XMM move requires a memory operand"),
            }
        }
        Ret if instruction.code() == Code::Retnq => Operation::Ret,
        Call if instruction.code() == Code::Call_rel32_64 => Operation::Call {
            target: instruction.near_branch_target(),
        },
        Syscall => Operation::Syscall,
        _ => bail!("unsupported instruction {:?}", instruction.code()),
    })
}
