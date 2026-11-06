use serde::{Deserialize, Serialize};

use crate::register::{Register32, Register64};
use Register32::*;
use Register64::*;
use strum::VariantArray;

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct Memory8 {
    pub base: Register64,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum Operation {
    Xor {
        destination: Register32,
        source: Register32,
    },
    Test {
        left: Register64,
        right: Register64,
    },
    Movzx {
        destination: Register32,
        source: Memory8,
    },
    Add {
        destination: Register64,
        source: Register64,
    },
    Inc {
        destination: Register64,
    },
    Dec {
        destination: Register64,
    },
    Jz {
        target: usize,
    },
    Jnz {
        target: usize,
    },
    Ret,
}
impl Operation {
    fn assembly(self) -> String {
        match self {
            Self::Xor {
                destination,
                source,
            } => format!("xor {destination}, {source}"),
            Self::Test { left, right } => format!("test {left}, {right}"),
            Self::Movzx {
                destination,
                source,
            } => format!("movzx {destination}, BYTE PTR [{}]", source.base),
            Self::Add {
                destination,
                source,
            } => format!("add {destination}, {source}"),
            Self::Inc { destination } => format!("inc {destination}"),
            Self::Dec { destination } => format!("dec {destination}"),
            Self::Jz { target } => format!("jz rivet_instruction_{target}"),
            Self::Jnz { target } => format!("jnz rivet_instruction_{target}"),
            Self::Ret => "ret".into(),
        }
    }
}
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Case {
    pub program: Vec<Operation>,
    pub registers: [u64; 16],
    pub zero_flag: bool,
    pub data: Vec<u8>,
    pub fault_memory: bool,
    pub steps: usize,
}
impl Case {
    pub fn assembly(&self) -> String {
        let mut source = String::new();
        for (index, operation) in self.program.iter().enumerate() {
            source.push_str(&format!(
                "rivet_instruction_{index}:\n    {}\n",
                operation.assembly()
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
    pub program: Vec<Operation>,
    pub registers: [u64; 16],
    pub zero_flag: bool,
    pub memory_base: u64,
    pub memory: Vec<u8>,
    pub steps: usize,
}

#[derive(Debug, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase", rename_all_fields = "camelCase")]
pub enum Status {
    Running { instruction_index: u64 },
    Returned { address: u64 },
    Fault,
    Outside { address: u64 },
    Signal { number: i32, address: u64 },
}
#[derive(Debug, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct Snapshot {
    pub registers: [u64; 16],
    pub zero_flag: bool,
    pub status: Status,
}

fn random_word(generator: &mut fastrand::Rng) -> u64 {
    const EDGES: [u64; 10] = [
        0,
        1,
        255,
        256,
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

fn binary_instruction<Operand: Copy>(
    generator: &mut fastrand::Rng,
    operands: &[Operand],
    instruction: fn(Operand, Operand) -> Operation,
) -> Operation {
    let destination = sample(generator, operands);
    let source = if generator.bool() {
        destination
    } else {
        sample(generator, operands)
    };
    instruction(destination, source)
}

fn random_instruction(generator: &mut fastrand::Rng) -> Operation {
    match generator.usize(..9) {
        0 => binary_instruction(generator, Register32::VARIANTS, |destination, source| {
            Operation::Xor {
                destination,
                source,
            }
        }),
        1 => binary_instruction(generator, Register64::VARIANTS, |left, right| {
            Operation::Test { left, right }
        }),
        2 => Operation::Movzx {
            destination: sample(generator, Register32::VARIANTS),
            source: Memory8 {
                base: sample(generator, Register64::VARIANTS),
            },
        },
        3 => binary_instruction(generator, Register64::VARIANTS, |destination, source| {
            Operation::Add {
                destination,
                source,
            }
        }),
        4 => Operation::Inc {
            destination: sample(generator, Register64::VARIANTS),
        },
        5 => Operation::Dec {
            destination: sample(generator, Register64::VARIANTS),
        },
        6 => Operation::Jz { target: 2 },
        7 => Operation::Jnz { target: 2 },
        _ => Operation::Ret,
    }
}

// Keep RSP as a return stack and use RDI as the data pointer in program cases.
fn random_program_instruction(generator: &mut fastrand::Rng, target: usize) -> Operation {
    match generator.usize(..9) {
        0 => Operation::Xor {
            destination: Eax,
            source: Eax,
        },
        1 => Operation::Test {
            left: Rsi,
            right: Rsi,
        },
        2 => Operation::Movzx {
            destination: Edx,
            source: Memory8 { base: Rdi },
        },
        3 => Operation::Add {
            destination: Rax,
            source: Rdx,
        },
        4 => Operation::Inc { destination: Rdi },
        5 => Operation::Dec { destination: Rsi },
        6 => Operation::Jz { target },
        7 => Operation::Jnz { target },
        _ => Operation::Ret,
    }
}

pub fn generate(generator: &mut fastrand::Rng) -> Case {
    let whole_program = generator.bool();
    let mut program = if whole_program {
        let count = generator.usize(1..9);
        (0..count)
            .map(|index| {
                let target = generator.usize(index + 1..=count);
                random_program_instruction(generator, target)
            })
            .collect()
    } else {
        vec![random_instruction(generator)]
    };
    if whole_program {
        // Forward branches may target this appended return instruction.
        program.push(Operation::Ret);
    } else if matches!(
        program.first(),
        Some(Operation::Jz { .. } | Operation::Jnz { .. })
    ) {
        program.extend([Operation::Inc { destination: Rdi }, Operation::Ret]);
    }
    Case {
        steps: if whole_program { program.len() + 1 } else { 1 },
        program,
        registers: std::array::from_fn(|_| random_word(generator)),
        zero_flag: generator.bool(),
        data: (0..generator.usize(1..33))
            .map(|_| generator.u8(..))
            .collect(),
        fault_memory: generator.bool(),
    }
}
