use rivet_import::operand::{Address, Operand, Scale, Width};
use rivet_import::{
    Instruction,
    program::{BinaryOp, Condition, Operation, ShiftOp, XmmMove},
};
use serde::{Deserialize, Serialize};

use crate::register::{Register32, Register64, Xmm};
use Register32::*;
use Register64::*;
use strum::{EnumCount, VariantArray};

// Excludes the appended return instruction.
const MAX_BODY_INSTRUCTIONS: usize = 8;
const MAX_DATA_BYTES: usize = 32;
const MAX_PROGRAM_STEPS: usize = 64;

pub fn memory_address(operation: &Operation) -> Option<&Address> {
    match operation {
        Operation::Binary {
            destination: Operand::Memory { address, .. },
            ..
        }
        | Operation::Binary {
            source: Operand::Memory { address, .. },
            ..
        }
        | Operation::Mov {
            destination: Operand::Memory { address, .. },
            ..
        }
        | Operation::Mov {
            source: Operand::Memory { address, .. },
            ..
        }
        | Operation::Not {
            destination: Operand::Memory { address, .. },
        }
        | Operation::Setcc {
            destination: Operand::Memory { address, .. },
            ..
        }
        | Operation::Cmovcc {
            source: Operand::Memory { address, .. },
            ..
        }
        | Operation::Imul {
            source: Operand::Memory { address, .. },
            ..
        }
        | Operation::Movzx {
            source: Operand::Memory { address, .. },
            ..
        }
        | Operation::Movsxd {
            source: Operand::Memory { address, .. },
            ..
        }
        | Operation::LoadXmm {
            source: address, ..
        }
        | Operation::StoreXmm {
            destination: address,
            ..
        } => Some(address),
        _ => None,
    }
}
fn assembly(operation: Operation) -> String {
    match operation {
        Operation::Binary {
            operation,
            destination,
            source,
        } => format!("{operation} {destination}, {source}"),
        Operation::Movzx {
            destination,
            source,
        } => format!("movzx {destination}, {source}"),
        Operation::Movsxd {
            destination,
            source,
        } => format!("movsxd {destination}, {source}"),
        Operation::Lea {
            destination,
            source,
        } => format!("lea {destination}, {source}"),
        Operation::Mov {
            destination,
            source,
        } => format!("mov {destination}, {source}"),
        Operation::Jmp { target } => format!("jmp rivet_instruction_{target}"),
        Operation::Jcc { condition, target } => format!("j{condition} rivet_instruction_{target}"),
        Operation::Setcc {
            condition,
            destination,
        } => format!("set{condition} {destination}"),
        Operation::Cmovcc {
            condition,
            destination,
            source,
        } => format!("cmov{condition} {destination}, {source}"),
        Operation::Inc { destination } => format!("inc {destination}"),
        Operation::Dec { destination } => format!("dec {destination}"),
        Operation::Ret => "ret".into(),
        Operation::Not { destination } => format!("not {destination}"),
        Operation::Imul {
            destination,
            source,
            immediate,
        } => match immediate {
            Some(value) => format!("imul {destination}, {source}, {value}"),
            None => format!("imul {destination}, {source}"),
        },
        Operation::Shift {
            operation,
            destination,
            count,
        } => format!("{operation} {destination}, {count}"),
        Operation::LoadXmm {
            operation,
            destination,
            source,
        } => format!("{operation} {destination}, XMMWORD PTR {source}"),
        Operation::StoreXmm {
            operation,
            destination,
            source,
        } => format!("{operation} XMMWORD PTR {destination}, {source}"),
        Operation::Movd {
            destination,
            source,
        } => format!("movd {destination}, {source}"),
        Operation::Pshufd {
            destination,
            source,
            order,
        } => format!("pshufd {destination}, {source}, {order}"),
        Operation::Push { source } => format!("push {source}"),
        Operation::Pop { destination } => format!("pop {destination}"),
    }
}
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Case {
    // Branch targets are instruction indices until assembly resolves the labels.
    pub program: Vec<Operation>,
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
impl Case {
    pub fn assembly(&self) -> String {
        let mut source = String::new();
        for (index, operation) in self.program.iter().enumerate() {
            source.push_str(&format!(
                "rivet_instruction_{index}:\n    {}\n",
                assembly(*operation)
            ));
        }
        source.push_str("rivet_end:\n");
        source
    }
}

// The same program and initial state are used by both runners.
#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ExecutionInput {
    pub program: Vec<Instruction>,
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
    Returned { address: u64 },
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

fn random_address(generator: &mut fastrand::Rng, whole_program: bool) -> Address {
    let base = if whole_program {
        Rdi
    } else {
        sample(generator, Register64::VARIANTS)
    };
    let index = if whole_program {
        Rbx
    } else {
        sample(generator, Register64::VARIANTS)
    };
    let index = (generator.bool() && index != Rsp && index != base).then_some(index);
    Address {
        base: if !whole_program && index.is_some() && generator.usize(..4) == 0 {
            None
        } else {
            Some(base)
        },
        index,
        scale: sample(generator, Scale::VARIANTS),
        displacement: sample(generator, &[-64, -8, -7, -1, 0, 1, 7, 8, 31, 63]),
    }
}

fn random_operands(
    generator: &mut fastrand::Rng,
    whole_program: bool,
    operation: Option<BinaryOp>,
) -> Operation {
    let width = sample(generator, Width::VARIANTS);
    let destination = if whole_program {
        Rcx
    } else {
        sample(generator, Register64::VARIANTS)
    };
    let source = if whole_program {
        Rdx
    } else if generator.bool() {
        destination
    } else {
        sample(generator, Register64::VARIANTS)
    };
    let register = Operand::register(width, destination);
    let source = Operand::register(width, source);
    let memory = Operand::Memory {
        width,
        address: random_address(generator, whole_program),
    };
    let form = generator.usize(..5);
    let sign_extended = width == Width::Qword && (form == 4 || operation.is_some());
    let bits = if sign_extended { 32 } else { width.bits() };
    let unsigned = (random_word(generator) as i128) & ((1i128 << bits) - 1);
    let value = if sign_extended || generator.bool() {
        if unsigned >= 1i128 << (bits - 1) {
            unsigned - (1i128 << bits)
        } else {
            unsigned
        }
    } else {
        unsigned
    };
    let immediate = Operand::Immediate { value };
    let (mut destination, mut source) = match form {
        0 => (register, source),
        1 => (register, immediate),
        2 => (register, memory),
        3 => (memory, source),
        4 => (memory, immediate),
        _ => unreachable!(),
    };
    if let Some(operation) = operation {
        if matches!(operation, BinaryOp::Test) && matches!(source, Operand::Memory { .. }) {
            std::mem::swap(&mut destination, &mut source);
        }
        Operation::Binary {
            operation,
            destination,
            source,
        }
    } else {
        Operation::Mov {
            destination,
            source,
        }
    }
}

fn register_or_memory(generator: &mut fastrand::Rng, width: Width, whole_program: bool) -> Operand {
    if generator.bool() {
        Operand::Memory {
            width,
            address: random_address(generator, whole_program),
        }
    } else {
        let register = if whole_program {
            Rdx
        } else {
            sample(generator, Register64::VARIANTS)
        };
        Operand::register(width, register)
    }
}

// Branching programs preserve the return stack and reserve RSI for countdowns.
fn random_instruction(
    generator: &mut fastrand::Rng,
    whole_program: bool,
    target: usize,
) -> Operation {
    let register = if whole_program {
        Rdi
    } else {
        sample(generator, Register64::VARIANTS)
    };
    match generator.usize(..Operation::COUNT - if whole_program { 2 } else { 0 }) {
        0 => {
            let operation = sample(generator, BinaryOp::VARIANTS);
            random_operands(generator, whole_program, Some(operation))
        }
        1 => Operation::Lea {
            destination: if whole_program { Rcx } else { register },
            source: random_address(generator, whole_program),
        },
        2 => {
            let width = sample(generator, &[Width::Byte, Width::Word]);
            Operation::Movzx {
                destination: if whole_program {
                    Edx
                } else {
                    sample(generator, Register32::VARIANTS)
                },
                source: register_or_memory(generator, width, whole_program),
            }
        }
        3 => Operation::Movsxd {
            destination: if whole_program { Rdx } else { register },
            source: register_or_memory(generator, Width::Dword, whole_program),
        },
        4 => random_operands(generator, whole_program, None),
        5 => Operation::Jmp {
            target: target as u64,
        },
        6 => Operation::Jcc {
            condition: sample(generator, Condition::VARIANTS),
            target: target as u64,
        },
        7 => Operation::Setcc {
            condition: sample(generator, Condition::VARIANTS),
            destination: if generator.bool() {
                Operand::register(Width::Byte, if whole_program { Rcx } else { register })
            } else {
                Operand::Memory {
                    width: Width::Byte,
                    address: random_address(generator, whole_program),
                }
            },
        },
        8 => {
            let width = sample(generator, &[Width::Word, Width::Dword, Width::Qword]);
            Operation::Cmovcc {
                condition: sample(generator, Condition::VARIANTS),
                destination: Operand::register(width, if whole_program { Rcx } else { register }),
                source: register_or_memory(generator, width, whole_program),
            }
        }
        9 => Operation::Inc {
            destination: register,
        },
        10 => Operation::Dec {
            destination: if whole_program { Rsi } else { register },
        },
        11 => Operation::Ret,
        12 => {
            let width = sample(generator, Width::VARIANTS);
            Operation::Not {
                destination: register_or_memory(generator, width, whole_program),
            }
        }
        13 => {
            let width = sample(generator, &[Width::Word, Width::Dword, Width::Qword]);
            let immediate = generator.bool().then(|| {
                let value = random_word(generator);
                if width == Width::Word {
                    value as i16 as i128
                } else {
                    value as i32 as i128
                }
            });
            Operation::Imul {
                destination: Operand::register(width, if whole_program { Rcx } else { register }),
                source: register_or_memory(generator, width, whole_program),
                immediate,
            }
        }
        14 => Operation::Shift {
            operation: sample(generator, ShiftOp::VARIANTS),
            destination: Operand::register(
                sample(generator, &[Width::Dword, Width::Qword]),
                if whole_program { Rcx } else { register },
            ),
            count: generator.u8(..),
        },
        15 => Operation::LoadXmm {
            operation: sample(generator, XmmMove::VARIANTS),
            destination: sample(generator, Xmm::VARIANTS),
            source: random_address(generator, whole_program),
        },
        16 => Operation::StoreXmm {
            operation: sample(generator, XmmMove::VARIANTS),
            destination: random_address(generator, whole_program),
            source: sample(generator, Xmm::VARIANTS),
        },
        17 => Operation::Movd {
            destination: sample(generator, Xmm::VARIANTS),
            source: sample(generator, Register32::VARIANTS),
        },
        18 => Operation::Pshufd {
            destination: sample(generator, Xmm::VARIANTS),
            source: sample(generator, Xmm::VARIANTS),
            order: generator.u8(..),
        },
        19 => Operation::Push { source: register },
        20 => Operation::Pop {
            destination: register,
        },
        _ => unreachable!(),
    }
}

pub fn generate(generator: &mut fastrand::Rng) -> Case {
    let whole_program = generator.bool();
    let mut program = if whole_program && generator.bool() {
        // Matched saves/restores keep RET on its original slot, including PUSH/POP RSP.
        let registers: Vec<_> = (0..generator.usize(1..=MAX_BODY_INSTRUCTIONS / 2))
            .map(|_| sample(generator, Register64::VARIANTS))
            .collect();
        registers
            .iter()
            .map(|&source| Operation::Push { source })
            .chain(
                registers
                    .iter()
                    .rev()
                    .map(|&destination| Operation::Pop { destination }),
            )
            .collect()
    } else if whole_program {
        let count = generator.usize(1..=MAX_BODY_INSTRUCTIONS);
        (0..count)
            .map(|_| {
                let target = generator.usize(0..=count);
                random_instruction(generator, true, target)
            })
            .collect()
    } else {
        vec![random_instruction(generator, false, 2)]
    };
    if whole_program {
        // Branches may also target this appended return instruction.
        program.push(Operation::Ret);
    } else if matches!(
        program.first(),
        Some(Operation::Jmp { .. } | Operation::Jcc { .. })
    ) {
        program.extend([Operation::Inc { destination: Rdi }, Operation::Ret]);
    }
    let mut registers = std::array::from_fn(|_| random_word(generator));
    if whole_program && generator.bool() {
        // The program generator decrements RSI; exercise short countdowns too.
        registers[Rsi as usize] = generator.u64(0..=MAX_BODY_INSTRUCTIONS as u64);
    }
    Case {
        steps: if whole_program { MAX_PROGRAM_STEPS } else { 1 },
        program,
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
    }
}
