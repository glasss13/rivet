use serde::{Deserialize, Serialize};

use crate::{
    operand::{Address, Operand, Scale, Width},
    register::{Register32, Register64},
};
use Register32::*;
use Register64::*;
use strum::{EnumCount, VariantArray};

// Excludes the appended return instruction.
const MAX_BODY_INSTRUCTIONS: usize = 8;
const MAX_DATA_BYTES: usize = 32;
const MAX_PROGRAM_STEPS: usize = 64;

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq, EnumCount)]
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
        source: Address,
    },
    Mov {
        destination: Operand,
        source: Operand,
    },
    Cmp {
        left: Register64,
        right: Register64,
    },
    Jb {
        target: usize,
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
    pub fn memory_address(&self) -> Option<&Address> {
        match self {
            Self::Movzx { source, .. } => Some(source),
            Self::Mov {
                destination: Operand::Memory { address, .. },
                ..
            }
            | Self::Mov {
                source: Operand::Memory { address, .. },
                ..
            } => Some(address),
            _ => None,
        }
    }
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
            } => format!("movzx {destination}, BYTE PTR {source}"),
            Self::Mov {
                destination,
                source,
            } => format!("mov {destination}, {source}"),
            Self::Cmp { left, right } => format!("cmp {left}, {right}"),
            Self::Jb { target } => format!("jb rivet_instruction_{target}"),
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
    pub carry_flag: bool,
    pub memory_base: u64,
    pub writable_base: u64,
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
    pub carry_flag: bool,
    pub status: Status,
    pub memory: Vec<u8>,
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

fn random_move(generator: &mut fastrand::Rng, whole_program: bool) -> Operation {
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
    let bits = if form == 4 && width == Width::Qword {
        32
    } else {
        width.bits()
    };
    let unsigned = (random_word(generator) as i128) & ((1i128 << bits) - 1);
    let value = if (form == 4 && width == Width::Qword) || generator.bool() {
        if unsigned >= 1i128 << (bits - 1) {
            unsigned - (1i128 << bits)
        } else {
            unsigned
        }
    } else {
        unsigned
    };
    let immediate = Operand::Immediate { value };
    let (destination, source) = match form {
        0 => (register, source),
        1 => (register, immediate),
        2 => (register, memory),
        3 => (memory, source),
        4 => (memory, immediate),
        _ => unreachable!(),
    };
    Operation::Mov {
        destination,
        source,
    }
}

fn random_instruction(generator: &mut fastrand::Rng) -> Operation {
    if generator.bool() {
        return random_move(generator, false);
    }
    match generator.usize(..Operation::COUNT) {
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
            source: random_address(generator, false),
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
        8 => random_move(generator, false),
        9 => binary_instruction(generator, Register64::VARIANTS, |left, right| {
            Operation::Cmp { left, right }
        }),
        10 => Operation::Jb { target: 2 },
        11 => Operation::Ret,
        _ => unreachable!(),
    }
}

// Keep RSP as a return stack and use RDI as the data pointer in program cases.
fn random_program_instruction(generator: &mut fastrand::Rng, target: usize) -> Operation {
    match generator.usize(..Operation::COUNT) {
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
            source: Address::base_only(Rdi),
        },
        3 => Operation::Add {
            destination: Rax,
            source: Rdx,
        },
        4 => Operation::Inc { destination: Rdi },
        5 => Operation::Dec { destination: Rsi },
        6 => Operation::Jz { target },
        7 => Operation::Jnz { target },
        8 => random_move(generator, true),
        9 => Operation::Cmp {
            left: Rax,
            right: Rdx,
        },
        10 => Operation::Jb { target },
        11 => Operation::Ret,
        _ => unreachable!(),
    }
}

pub fn generate(generator: &mut fastrand::Rng) -> Case {
    let whole_program = generator.bool();
    let mut program = if whole_program {
        let count = generator.usize(1..=MAX_BODY_INSTRUCTIONS);
        (0..count)
            .map(|_| {
                let target = generator.usize(0..=count);
                random_program_instruction(generator, target)
            })
            .collect()
    } else {
        vec![random_instruction(generator)]
    };
    if whole_program {
        // Branches may also target this appended return instruction.
        program.push(Operation::Ret);
    } else if matches!(
        program.first(),
        Some(Operation::Jz { .. } | Operation::Jnz { .. } | Operation::Jb { .. })
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
        zero_flag: generator.bool(),
        carry_flag: generator.bool(),
        data: (0..generator.usize(1..=MAX_DATA_BYTES))
            .map(|_| generator.u8(..))
            .collect(),
        fault_memory: generator.bool(),
        read_only_data: generator.bool(),
    }
}
