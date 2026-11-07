//! Encode generated cases with iced. The shared importer still decodes the resulting bytes.
use anyhow::{Context, Result, bail, ensure};
use iced_x86::{BlockEncoderOptions, code_asm::*};
use rivet_import::{
    operand::{Address, Operand, Width},
    program::{BinaryOp, Condition, Operation, ShiftOp, XmmMove},
    register::*,
};

fn reg8(register: Register8) -> AsmRegister8 {
    [
        al, bl, cl, dl, sil, dil, bpl, spl, r8b, r9b, r10b, r11b, r12b, r13b, r14b, r15b,
    ][register as usize]
}
fn reg16(register: Register16) -> AsmRegister16 {
    [
        ax, bx, cx, dx, si, di, bp, sp, r8w, r9w, r10w, r11w, r12w, r13w, r14w, r15w,
    ][register as usize]
}
fn reg32(register: Register32) -> AsmRegister32 {
    [
        eax, ebx, ecx, edx, esi, edi, ebp, esp, r8d, r9d, r10d, r11d, r12d, r13d, r14d, r15d,
    ][register as usize]
}
fn reg64(register: Register64) -> AsmRegister64 {
    [
        rax, rbx, rcx, rdx, rsi, rdi, rbp, rsp, r8, r9, r10, r11, r12, r13, r14, r15,
    ][register as usize]
}
fn xmm(register: Xmm) -> AsmRegisterXmm {
    [
        xmm0, xmm1, xmm2, xmm3, xmm4, xmm5, xmm6, xmm7, xmm8, xmm9, xmm10, xmm11, xmm12, xmm13,
        xmm14, xmm15,
    ][register as usize]
}

fn memory(address: Address) -> AsmMemoryOperand {
    let mut value = ptr(address.displacement);
    if let Some(base) = address.base {
        value = value + reg64(base);
    }
    if let Some(index) = address.index {
        value = value + reg64(index) * address.scale.value() as u32;
    }
    value
}
fn sized_memory(width: Width, address: Address) -> AsmMemoryOperand {
    match width {
        Width::Byte => byte_ptr(memory(address)),
        Width::Word => word_ptr(memory(address)),
        Width::Dword => dword_ptr(memory(address)),
        Width::Qword => qword_ptr(memory(address)),
    }
}

pub fn program(operations: &[Operation]) -> Result<(Vec<u8>, Vec<u64>)> {
    ensure!(!operations.is_empty(), "empty generated program");
    let mut assembler = CodeAssembler::new(64)?;
    let mut labels: Vec<_> = operations
        .iter()
        .map(|_| assembler.create_label())
        .collect();
    for (index, &operation) in operations.iter().enumerate() {
        assembler.set_label(&mut labels[index])?;
        emit(&mut assembler, operation, &labels)
            .with_context(|| format!("encoding instruction {index}"))?;
    }
    // All generated branches are internal and memory operands use registers, so
    // the block is position-independent and can be copied into its native mapping.
    let result = assembler
        .assemble_options(0, BlockEncoderOptions::RETURN_NEW_INSTRUCTION_OFFSETS)?
        .inner;
    ensure!(
        result
            .new_instruction_offsets
            .iter()
            .all(|&offset| offset != u32::MAX),
        "unexpected instruction expansion"
    );
    let offsets = result
        .new_instruction_offsets
        .into_iter()
        .map(u64::from)
        .chain(std::iter::once(result.code_buffer.len() as u64))
        .collect();
    Ok((result.code_buffer, offsets))
}

fn emit(assembler: &mut CodeAssembler, operation: Operation, labels: &[CodeLabel]) -> Result<()> {
    use Operand::*;
    // Dispatch runtime operand widths to iced's typed assembler methods.
    macro_rules! load {
        (test, $reg:expr, $mem:expr) => {
            assembler.test($mem, $reg)
        };
        ($method:ident, $reg:expr, $mem:expr) => {
            assembler.$method($reg, $mem)
        };
    }
    macro_rules! binary {
        ($method:ident, $destination:expr, $source:expr, $wide:ty) => {
            match ($destination, $source) {
                (Reg8 { register: dest }, Reg8 { register: src }) => {
                    assembler.$method(reg8(dest), reg8(src))
                }
                (Reg8 { register }, Memory { width, address }) => {
                    load!($method, reg8(register), sized_memory(width, address))
                }
                (Memory { width, address }, Reg8 { register }) => {
                    assembler.$method(sized_memory(width, address), reg8(register))
                }
                (Reg8 { register }, Immediate { value }) => {
                    assembler.$method(reg8(register), value as i32)
                }
                (Reg16 { register: dest }, Reg16 { register: src }) => {
                    assembler.$method(reg16(dest), reg16(src))
                }
                (Reg16 { register }, Memory { width, address }) => {
                    load!($method, reg16(register), sized_memory(width, address))
                }
                (Memory { width, address }, Reg16 { register }) => {
                    assembler.$method(sized_memory(width, address), reg16(register))
                }
                (Reg16 { register }, Immediate { value }) => {
                    assembler.$method(reg16(register), value as i32)
                }
                (Reg32 { register: dest }, Reg32 { register: src }) => {
                    assembler.$method(reg32(dest), reg32(src))
                }
                (Reg32 { register }, Memory { width, address }) => {
                    load!($method, reg32(register), sized_memory(width, address))
                }
                (Memory { width, address }, Reg32 { register }) => {
                    assembler.$method(sized_memory(width, address), reg32(register))
                }
                (Reg32 { register }, Immediate { value }) => {
                    assembler.$method(reg32(register), value as i32)
                }
                (Reg64 { register: dest }, Reg64 { register: src }) => {
                    assembler.$method(reg64(dest), reg64(src))
                }
                (Reg64 { register }, Memory { width, address }) => {
                    load!($method, reg64(register), sized_memory(width, address))
                }
                (Memory { width, address }, Reg64 { register }) => {
                    assembler.$method(sized_memory(width, address), reg64(register))
                }
                (Reg64 { register }, Immediate { value }) => {
                    assembler.$method(reg64(register), value as $wide)
                }
                (Memory { width, address }, Immediate { value }) => {
                    assembler.$method(sized_memory(width, address), value as i32)
                }
                _ => bail!("unsupported generated operand pair"),
            }
        };
    }
    macro_rules! unary {
        ($method:ident, $operand:expr) => {
            match $operand {
                Reg8 { register } => assembler.$method(reg8(register)),
                Reg16 { register } => assembler.$method(reg16(register)),
                Reg32 { register } => assembler.$method(reg32(register)),
                Reg64 { register } => assembler.$method(reg64(register)),
                Memory { width, address } => assembler.$method(sized_memory(width, address)),
                _ => bail!("expected a writable operand"),
            }
        };
    }
    macro_rules! cmov {
        ($method:ident, $destination:expr, $source:expr) => {
            match ($destination, $source) {
                (Reg16 { register: dest }, Reg16 { register: src }) => {
                    assembler.$method(reg16(dest), reg16(src))
                }
                (Reg16 { register }, Memory { width, address }) => {
                    assembler.$method(reg16(register), sized_memory(width, address))
                }
                (Reg32 { register: dest }, Reg32 { register: src }) => {
                    assembler.$method(reg32(dest), reg32(src))
                }
                (Reg32 { register }, Memory { width, address }) => {
                    assembler.$method(reg32(register), sized_memory(width, address))
                }
                (Reg64 { register: dest }, Reg64 { register: src }) => {
                    assembler.$method(reg64(dest), reg64(src))
                }
                (Reg64 { register }, Memory { width, address }) => {
                    assembler.$method(reg64(register), sized_memory(width, address))
                }
                _ => bail!("unsupported conditional move operands"),
            }
        };
    }
    macro_rules! set {
        ($method:ident, $operand:expr) => {
            match $operand {
                Reg8 { register } => assembler.$method(reg8(register)),
                Memory {
                    width: Width::Byte,
                    address,
                } => assembler.$method(byte_ptr(memory(address))),
                _ => bail!("SETcc requires a byte operand"),
            }
        };
    }
    match operation {
        Operation::Binary {
            operation: BinaryOp::Add,
            destination,
            source,
        } => binary!(add, destination, source, i32)?,
        Operation::Binary {
            operation: BinaryOp::Sub,
            destination,
            source,
        } => binary!(sub, destination, source, i32)?,
        Operation::Binary {
            operation: BinaryOp::Sbb,
            destination,
            source,
        } => binary!(sbb, destination, source, i32)?,
        Operation::Binary {
            operation: BinaryOp::Cmp,
            destination,
            source,
        } => binary!(cmp, destination, source, i32)?,
        Operation::Binary {
            operation: BinaryOp::Test,
            destination,
            source,
        } => binary!(test, destination, source, i32)?,
        Operation::Binary {
            operation: BinaryOp::And,
            destination,
            source,
        } => binary!(and, destination, source, i32)?,
        Operation::Binary {
            operation: BinaryOp::Or,
            destination,
            source,
        } => binary!(or, destination, source, i32)?,
        Operation::Binary {
            operation: BinaryOp::Xor,
            destination,
            source,
        } => binary!(xor, destination, source, i32)?,
        Operation::Mov {
            destination,
            source,
        } => binary!(mov, destination, source, i64)?,
        Operation::Not { destination } => unary!(not, destination)?,
        Operation::Lea {
            destination,
            source,
        } => assembler.lea(reg64(destination), memory(source))?,
        Operation::Movzx {
            destination,
            source,
        } => match source {
            Reg8 { register } => assembler.movzx(reg32(destination), reg8(register))?,
            Reg16 { register } => assembler.movzx(reg32(destination), reg16(register))?,
            Memory { width, address } => {
                assembler.movzx(reg32(destination), sized_memory(width, address))?
            }
            _ => bail!("unsupported MOVZX source"),
        },
        Operation::Movsxd {
            destination,
            source,
        } => match source {
            Reg32 { register } => assembler.movsxd(reg64(destination), reg32(register))?,
            Memory {
                width: Width::Dword,
                address,
            } => assembler.movsxd(reg64(destination), dword_ptr(memory(address)))?,
            _ => bail!("unsupported MOVSXD source"),
        },
        Operation::Inc { destination } => assembler.inc(reg64(destination))?,
        Operation::Dec { destination } => assembler.dec(reg64(destination))?,
        Operation::Pop { destination } => assembler.pop(reg64(destination))?,
        Operation::Push { source } => assembler.push(reg64(source))?,
        Operation::Ret => assembler.ret()?,
        Operation::Jmp { target } => assembler.jmp(
            *labels
                .get(target as usize)
                .context("invalid branch target")?,
        )?,
        Operation::Jcc { condition, target } => {
            let label = *labels
                .get(target as usize)
                .context("invalid branch target")?;
            match condition {
                Condition::Equal => assembler.je(label)?,
                Condition::NotEqual => assembler.jne(label)?,
                Condition::Below => assembler.jb(label)?,
                Condition::AboveOrEqual => assembler.jae(label)?,
                Condition::BelowOrEqual => assembler.jbe(label)?,
                Condition::Above => assembler.ja(label)?,
                Condition::Sign => assembler.js(label)?,
            }
        }
        Operation::Setcc {
            condition,
            destination,
        } => match condition {
            Condition::Equal => set!(sete, destination)?,
            Condition::NotEqual => set!(setne, destination)?,
            Condition::Below => set!(setb, destination)?,
            Condition::AboveOrEqual => set!(setae, destination)?,
            Condition::BelowOrEqual => set!(setbe, destination)?,
            Condition::Above => set!(seta, destination)?,
            Condition::Sign => set!(sets, destination)?,
        },
        Operation::Cmovcc {
            condition,
            destination,
            source,
        } => match condition {
            Condition::Equal => cmov!(cmove, destination, source)?,
            Condition::NotEqual => cmov!(cmovne, destination, source)?,
            Condition::Below => cmov!(cmovb, destination, source)?,
            Condition::AboveOrEqual => cmov!(cmovae, destination, source)?,
            Condition::BelowOrEqual => cmov!(cmovbe, destination, source)?,
            Condition::Above => cmov!(cmova, destination, source)?,
            Condition::Sign => cmov!(cmovs, destination, source)?,
        },
        Operation::Shift {
            operation,
            destination,
            count,
        } => match (operation, destination) {
            (ShiftOp::Shl, Reg32 { register }) => assembler.shl(reg32(register), count as u32)?,
            (ShiftOp::Shl, Reg64 { register }) => assembler.shl(reg64(register), count as u32)?,
            (ShiftOp::Shr, Reg32 { register }) => assembler.shr(reg32(register), count as u32)?,
            (ShiftOp::Shr, Reg64 { register }) => assembler.shr(reg64(register), count as u32)?,
            _ => bail!("unsupported shift destination"),
        },
        Operation::Imul {
            destination,
            source,
            immediate,
        } => {
            macro_rules! multiply {
                ($dest:expr, $src:expr) => {
                    match immediate {
                        Some(value) => assembler.imul_3($dest, $src, value as i32)?,
                        None => assembler.imul_2($dest, $src)?,
                    }
                };
            }
            match (destination, source) {
                (Reg16 { register: dest }, Reg16 { register: src }) => {
                    multiply!(reg16(dest), reg16(src))
                }
                (Reg16 { register }, Memory { width, address }) => {
                    multiply!(reg16(register), sized_memory(width, address))
                }
                (Reg32 { register: dest }, Reg32 { register: src }) => {
                    multiply!(reg32(dest), reg32(src))
                }
                (Reg32 { register }, Memory { width, address }) => {
                    multiply!(reg32(register), sized_memory(width, address))
                }
                (Reg64 { register: dest }, Reg64 { register: src }) => {
                    multiply!(reg64(dest), reg64(src))
                }
                (Reg64 { register }, Memory { width, address }) => {
                    multiply!(reg64(register), sized_memory(width, address))
                }
                _ => bail!("unsupported IMUL operands"),
            }
        }
        Operation::LoadXmm {
            operation: XmmMove::Movups,
            destination,
            source,
        } => assembler.movups(xmm(destination), xmmword_ptr(memory(source)))?,
        Operation::StoreXmm {
            operation: XmmMove::Movups,
            destination,
            source,
        } => assembler.movups(xmmword_ptr(memory(destination)), xmm(source))?,
        Operation::LoadXmm {
            operation: XmmMove::Movdqu,
            destination,
            source,
        } => assembler.movdqu(xmm(destination), xmmword_ptr(memory(source)))?,
        Operation::StoreXmm {
            operation: XmmMove::Movdqu,
            destination,
            source,
        } => assembler.movdqu(xmmword_ptr(memory(destination)), xmm(source))?,
        Operation::Movd {
            destination,
            source,
        } => assembler.movd(xmm(destination), reg32(source))?,
        Operation::Pshufd {
            destination,
            source,
            order,
        } => assembler.pshufd(xmm(destination), xmm(source), order as u32)?,
    }
    Ok(())
}
