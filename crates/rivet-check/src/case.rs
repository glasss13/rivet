use crate::register::Register64::{Rcx, Rdx, Rsi};
use anyhow::{Result, ensure};
use iced_x86::{BlockEncoderOptions, code_asm::*};
use rivet_import::Instruction;
use serde::{Deserialize, Serialize};

// Register order matches the native and Lean initial-state arrays.
pub const REGISTERS: [AsmRegister64; 16] = [
    rax, rbx, rcx, rdx, rsi, rdi, rbp, rsp, r8, r9, r10, r11, r12, r13, r14, r15,
];
const REGISTERS8: [AsmRegister8; 16] = [
    al, bl, cl, dl, sil, dil, bpl, spl, r8b, r9b, r10b, r11b, r12b, r13b, r14b, r15b,
];
const REGISTERS16: [AsmRegister16; 16] = [
    ax, bx, cx, dx, si, di, bp, sp, r8w, r9w, r10w, r11w, r12w, r13w, r14w, r15w,
];
const REGISTERS32: [AsmRegister32; 16] = [
    eax, ebx, ecx, edx, esi, edi, ebp, esp, r8d, r9d, r10d, r11d, r12d, r13d, r14d, r15d,
];
const XMM: [AsmRegisterXmm; 16] = [
    xmm0, xmm1, xmm2, xmm3, xmm4, xmm5, xmm6, xmm7, xmm8, xmm9, xmm10, xmm11, xmm12, xmm13, xmm14,
    xmm15,
];
const MAX_BODY_INSTRUCTIONS: usize = 8;
const MAX_DATA_BYTES: usize = 32;
const MAX_PROGRAM_STEPS: usize = 64;

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Case {
    pub code: Vec<u8>,
    // Encoder offsets, including the end of the block, for native boundary checks.
    pub offsets: Vec<u64>,
    pub registers: [u64; 16],
    pub xmm_registers: [[u32; 4]; 16],
    pub sign_flag: bool,
    pub zero_flag: bool,
    pub carry_flag: bool,
    pub data: Vec<u8>,
    pub fault_memory: bool,
    pub read_only_data: bool,
    pub steps: usize,
}
// The same program and initial state are used by both runners.
#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ExecutionInput {
    pub program: Vec<Instruction>,
    pub stop_address: u64,
    pub registers: [u64; 16],
    pub xmm_registers: [[u32; 4]; 16],
    pub sign_flag: bool,
    pub zero_flag: bool,
    pub carry_flag: bool,
    pub memory_base: u64,
    pub writable_base: u64,
    pub memory: Vec<u8>,
    pub steps: usize,
}

#[derive(Debug, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase", rename_all_fields = "camelCase")]
pub enum Status {
    Running { address: u64 },
    Fault,
    Outside { address: u64 },
    Signal { number: i32, address: u64 },
}
#[derive(Debug, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct Snapshot {
    pub registers: [u64; 16],
    pub xmm_registers: [[u32; 4]; 16],
    pub sign_flag: bool,
    pub zero_flag: bool,
    pub carry_flag: bool,
    pub status: Status,
    pub memory: Vec<u8>,
}

fn random_word(generator: &mut fastrand::Rng) -> u64 {
    const EDGES: [u64; 18] = [
        0,
        1,
        127,
        128,
        255,
        256,
        (1 << 15) - 1,
        1 << 15,
        u16::MAX as u64,
        1 << 16,
        (1 << 31) - 1,
        1 << 31,
        u32::MAX as u64,
        1 << 32,
        (1 << 63) - 1,
        1 << 63,
        u64::MAX - 1,
        u64::MAX,
    ];
    if generator.usize(..5) < 3 {
        EDGES[generator.usize(..EDGES.len())]
    } else {
        generator.u64(..)
    }
}
fn sample<Operand: Copy>(generator: &mut fastrand::Rng, operands: &[Operand]) -> Operand {
    operands[generator.usize(..operands.len())]
}

fn random_address(generator: &mut fastrand::Rng, whole_program: bool) -> AsmMemoryOperand {
    let base = if whole_program {
        rdi
    } else {
        sample(generator, &REGISTERS)
    };
    let index = if whole_program {
        rbx
    } else {
        sample(generator, &REGISTERS)
    };
    let indexed = generator.bool() && index != rsp && index != base;
    let mut address = ptr(sample(generator, &[-64i64, -8, -7, -1, 0, 1, 7, 8, 31, 63]));
    if whole_program || !indexed || generator.usize(..4) != 0 {
        address = address + base;
    }
    if indexed {
        address = address + index * sample(generator, &[1u32, 2, 4, 8]);
    }
    address
}

// Each arm emits directly into iced; there is no intermediate Rivet operation.
fn random_instruction(
    assembler: &mut CodeAssembler,
    generator: &mut fastrand::Rng,
    whole_program: bool,
    target: CodeLabel,
) -> Result<()> {
    let destination = if whole_program {
        Rcx as usize
    } else {
        generator.usize(..16)
    };
    let source = if whole_program {
        Rdx as usize
    } else if generator.bool() {
        destination
    } else {
        generator.usize(..16)
    };
    let address = random_address(generator, whole_program);
    let value = random_word(generator);
    let form = generator.usize(..5);
    macro_rules! load {
        (test, $register:expr, $memory:expr) => {
            assembler.test($memory, $register)
        };
        ($method:ident, $register:expr, $memory:expr) => {
            assembler.$method($register, $memory)
        };
    }
    macro_rules! binary {
        ($registers:ident, $memory:ident, $narrow:ty, $mov:ty) => {{
            let dest = $registers[destination];
            let src = $registers[source];
            let mem = $memory(address);
            macro_rules! emit {
                ($method:ident, $immediate:ty) => {
                    match form {
                        0 => assembler.$method(dest, src),
                        1 => assembler.$method(dest, value as $narrow as $immediate),
                        2 => load!($method, dest, mem),
                        3 => assembler.$method(mem, src),
                        _ => assembler.$method(mem, value as $narrow as i32),
                    }
                };
            }
            match generator.usize(..9) {
                0 => emit!(add, i32)?,
                1 => emit!(sub, i32)?,
                2 => emit!(sbb, i32)?,
                3 => emit!(cmp, i32)?,
                4 => emit!(test, i32)?,
                5 => emit!(and, i32)?,
                6 => emit!(or, i32)?,
                7 => emit!(xor, i32)?,
                _ => emit!(mov, $mov)?,
            }
        }};
    }
    // Select register/memory source at generation time, keeping iced operands typed.
    macro_rules! source {
        ($method:ident, $destination:expr, $register:expr, $memory:expr $(, $extra:expr)?) => {
            if generator.bool() { assembler.$method($destination, $register $(, $extra)?)?; }
            else { assembler.$method($destination, $memory $(, $extra)?)?; }
        };
    }
    macro_rules! condition {
        ($emit:ident; $equal:ident, $not_equal:ident, $below:ident, $above_equal:ident, $below_equal:ident, $above:ident, $sign:ident) => {
            match generator.usize(..7) {
                0 => $emit!($equal),
                1 => $emit!($not_equal),
                2 => $emit!($below),
                3 => $emit!($above_equal),
                4 => $emit!($below_equal),
                5 => $emit!($above),
                _ => $emit!($sign),
            }
        };
    }
    match generator.usize(..if whole_program { 19 } else { 21 }) {
        0 => match generator.usize(..4) {
            0 => binary!(REGISTERS8, byte_ptr, i8, i32),
            1 => binary!(REGISTERS16, word_ptr, i16, i32),
            2 => binary!(REGISTERS32, dword_ptr, i32, i32),
            _ => binary!(REGISTERS, qword_ptr, i64, i64),
        },
        1 => assembler.lea(REGISTERS[destination], address)?,
        2 => {
            if generator.bool() {
                source!(
                    movzx,
                    REGISTERS32[destination],
                    REGISTERS8[source],
                    byte_ptr(address)
                );
            } else {
                source!(
                    movzx,
                    REGISTERS32[destination],
                    REGISTERS16[source],
                    word_ptr(address)
                );
            }
        }
        3 => {
            source!(
                movsxd,
                REGISTERS[destination],
                REGISTERS32[source],
                dword_ptr(address)
            );
        }
        4 => assembler.jmp(target)?,
        5 => {
            macro_rules! emit {
                ($method:ident) => {
                    assembler.$method(target)?
                };
            }
            condition!(emit; je, jne, jb, jae, jbe, ja, js);
        }
        6 => {
            macro_rules! emit {
                ($method:ident) => {
                    if generator.bool() {
                        assembler.$method(REGISTERS8[destination])?;
                    } else {
                        assembler.$method(byte_ptr(address))?;
                    }
                };
            }
            condition!(emit; sete, setne, setb, setae, setbe, seta, sets);
        }
        7 => {
            macro_rules! emit {
                ($method:ident) => {
                    match generator.usize(..3) {
                        0 => {
                            source!(
                                $method,
                                REGISTERS16[destination],
                                REGISTERS16[source],
                                word_ptr(address)
                            );
                        }
                        1 => {
                            source!(
                                $method,
                                REGISTERS32[destination],
                                REGISTERS32[source],
                                dword_ptr(address)
                            );
                        }
                        _ => {
                            source!(
                                $method,
                                REGISTERS[destination],
                                REGISTERS[source],
                                qword_ptr(address)
                            );
                        }
                    }
                };
            }
            condition!(emit; cmove, cmovne, cmovb, cmovae, cmovbe, cmova, cmovs);
        }
        8 => assembler.inc(if whole_program {
            rdi
        } else {
            REGISTERS[destination]
        })?,
        9 => assembler.dec(if whole_program {
            rsi
        } else {
            REGISTERS[destination]
        })?,
        10 => assembler.ret()?,
        11 => {
            macro_rules! emit {
                ($registers:ident, $memory:ident) => {
                    if generator.bool() {
                        assembler.not($registers[destination])?;
                    } else {
                        assembler.not($memory(address))?;
                    }
                };
            }
            match generator.usize(..4) {
                0 => emit!(REGISTERS8, byte_ptr),
                1 => emit!(REGISTERS16, word_ptr),
                2 => emit!(REGISTERS32, dword_ptr),
                _ => emit!(REGISTERS, qword_ptr),
            }
        }
        12 => {
            macro_rules! emit {
                ($registers:ident, $memory:ident, $immediate:expr) => {
                    if generator.bool() {
                        source!(
                            imul_3,
                            $registers[destination],
                            $registers[source],
                            $memory(address),
                            $immediate
                        );
                    } else {
                        source!(
                            imul_2,
                            $registers[destination],
                            $registers[source],
                            $memory(address)
                        );
                    }
                };
            }
            match generator.usize(..3) {
                0 => emit!(REGISTERS16, word_ptr, value as i16 as i32),
                1 => emit!(REGISTERS32, dword_ptr, value as i32),
                _ => emit!(REGISTERS, qword_ptr, value as i32),
            }
        }
        13 => {
            let count = generator.u8(..) as u32;
            match (generator.bool(), generator.bool()) {
                (true, true) => assembler.shl(REGISTERS32[destination], count)?,
                (true, false) => assembler.shr(REGISTERS32[destination], count)?,
                (false, true) => assembler.shl(REGISTERS[destination], count)?,
                (false, false) => assembler.shr(REGISTERS[destination], count)?,
            }
        }
        kind @ (14 | 15) => {
            let xmm = sample(generator, &XMM);
            match (kind == 14, generator.bool()) {
                (true, true) => assembler.movups(xmm, xmmword_ptr(address))?,
                (false, true) => assembler.movups(xmmword_ptr(address), xmm)?,
                (true, false) => assembler.movdqu(xmm, xmmword_ptr(address))?,
                (false, false) => assembler.movdqu(xmmword_ptr(address), xmm)?,
            }
        }
        16 => assembler.movd(sample(generator, &XMM), REGISTERS32[source])?,
        17 => assembler.pshufd(
            sample(generator, &XMM),
            sample(generator, &XMM),
            generator.u8(..) as u32,
        )?,
        18 => {
            if generator.bool() {
                assembler.nop()?;
            } else {
                assembler.nop_1(dword_ptr(address))?;
            }
        }
        19 => assembler.push(REGISTERS[destination])?,
        20 => assembler.pop(REGISTERS[destination])?,
        _ => unreachable!(),
    }
    Ok(())
}

pub fn generate(generator: &mut fastrand::Rng) -> Result<Case> {
    let whole_program = generator.bool();
    let mut assembler = CodeAssembler::new(64)?;
    if whole_program && generator.bool() {
        let mut functions: Vec<_> = (0..generator.usize(2..=MAX_BODY_INSTRUCTIONS))
            .map(|_| assembler.create_label())
            .collect();
        for index in 0..functions.len() {
            assembler.set_label(&mut functions[index])?;
            if index + 1 < functions.len() {
                assembler.call(functions[index + 1])?;
                if generator.bool() {
                    assembler.call(functions[generator.usize(index + 1..functions.len())])?;
                }
            }
            assembler.add(rax, generator.i32(..))?;
            assembler.ret()?;
        }
    } else if whole_program && generator.bool() {
        let registers: Vec<_> = (0..generator.usize(1..=MAX_BODY_INSTRUCTIONS / 2))
            .map(|_| sample(generator, &REGISTERS))
            .collect();
        for &register in &registers {
            assembler.push(register)?;
        }
        for &register in registers.iter().rev() {
            assembler.pop(register)?;
        }
        assembler.ret()?;
    } else {
        let count = if whole_program {
            generator.usize(1..=MAX_BODY_INSTRUCTIONS)
        } else {
            1
        };
        let mut labels: Vec<_> = (0..count + 2).map(|_| assembler.create_label()).collect();
        for index in 0..count {
            assembler.set_label(&mut labels[index])?;
            let target = if whole_program {
                generator.usize(0..=count)
            } else {
                2
            };
            random_instruction(&mut assembler, generator, whole_program, labels[target])?;
        }
        if whole_program {
            assembler.set_label(&mut labels[count])?;
            assembler.ret()?;
        } else if assembler.instructions()[0].is_jmp_short_or_near()
            || assembler.instructions()[0].is_jcc_short_or_near()
        {
            assembler.set_label(&mut labels[1])?;
            assembler.inc(rdi)?;
            assembler.set_label(&mut labels[2])?;
            assembler.ret()?;
        }
    }
    let encoded = assembler
        .assemble_options(0, BlockEncoderOptions::RETURN_NEW_INSTRUCTION_OFFSETS)?
        .inner;
    ensure!(
        encoded
            .new_instruction_offsets
            .iter()
            .all(|&offset| offset != u32::MAX),
        "unexpected instruction expansion"
    );
    let offsets = encoded
        .new_instruction_offsets
        .into_iter()
        .map(u64::from)
        .chain(std::iter::once(encoded.code_buffer.len() as u64))
        .collect();
    let mut registers = std::array::from_fn(|_| random_word(generator));
    if whole_program && generator.bool() {
        registers[Rsi as usize] = generator.u64(0..=MAX_BODY_INSTRUCTIONS as u64);
    }
    Ok(Case {
        code: encoded.code_buffer,
        offsets,
        steps: if whole_program { MAX_PROGRAM_STEPS } else { 1 },
        registers,
        xmm_registers: std::array::from_fn(|_| std::array::from_fn(|_| generator.u32(..))),
        sign_flag: generator.bool(),
        zero_flag: generator.bool(),
        carry_flag: generator.bool(),
        data: (0..generator.usize(1..=MAX_DATA_BYTES))
            .map(|_| generator.u8(..))
            .collect(),
        fault_memory: generator.bool(),
        read_only_data: generator.bool(),
    })
}
