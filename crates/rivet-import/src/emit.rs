use crate::elf::Image;
use anyhow::{Result, ensure};
use rivet_import::{
    Instruction,
    operand::{Address, Operand},
    program::Operation,
};
use std::fmt::Write;

pub fn module(bytes: &[u8], image: &Image, namespace: &str) -> Result<String> {
    ensure!(
        !namespace.is_empty()
            && namespace.split('.').all(|part| !part.is_empty()
                && !part.chars().any(|c| c == '«' || c == '»' || c.is_control())),
        "invalid Lean namespace"
    );
    let namespace = namespace
        .split('.')
        .map(|part| format!("«{part}»"))
        .collect::<Vec<_>>()
        .join(".");
    let mut source =
        format!("module\npublic import Rivet\n@[expose] public section\nnamespace {namespace}\n");
    let mut pages = Vec::new();
    for (index, page) in bytes.chunks(4096).enumerate() {
        let name = format!("file.page_{index}");
        write!(source, "\ndef {name} : Nat := 0x")?;
        let significant = page.iter().rposition(|&byte| byte != 0).unwrap_or(0);
        for byte in page[..=significant].iter().rev() {
            write!(source, "{byte:02x}")?;
        }
        writeln!(source)?;
        pages.push(name);
    }
    writeln!(
        source,
        "def file : Rivet.Exe := {{ size := {}, pages := [{}] }}",
        bytes.len(),
        pages.join(", ")
    )?;
    let mut names = Vec::new();
    for segment in &image.segments {
        let a = segment.address;
        let start = segment.start;
        let skip = a - start;
        let length = segment.length;
        let size = segment.size;
        let writable = segment.writable;
        let name = format!("segment_{a:x}");
        writeln!(
            source,
            "\nabbrev {name} : Rivet.Segment where\n  start := {start:#x}#64\n  length := {length}\n  writable := {writable}\n  executable := {}\n  skip := {skip}\n  size := {size}\n  fileOffset := {}\n  fileSize := {}",
            segment.executable,
            segment.offset,
            segment.bytes.len()
        )?;
        writeln!(
            source,
            "abbrev region_{a:x} : Rivet.Region := Rivet.Region.root {start:#x}#64 {length} true {writable}"
        )?;
        writeln!(
            source,
            "abbrev bytes_{a:x} : Rivet.Region := region_{a:x}.part {skip} {size}"
        )?;
        names.push(name);
    }
    writeln!(
        source,
        "\ndef layout : Rivet.Layout := {{ entry := {:#x}#64, segments := [{}] }}",
        image.entry,
        names.join(", ")
    )?;
    writeln!(
        source,
        "theorem layout_ok : file.layout = some layout := by decide +kernel"
    )?;
    ensure!(
        image
            .program
            .windows(2)
            .all(|pair| pair[0].address < pair[1].address),
        "instruction addresses must be strictly increasing"
    );
    program(&mut source, &image.program)?;
    writeln!(source, "\nend {namespace}")?;
    Ok(source)
}

/// Emits `program` as a balanced search tree over leaves of up to 16 instructions, so that a
/// proof fetches any instruction in a few comparisons and a scan of one leaf.
///
/// `program.leaf_<a>` is the leaf whose first instruction is at address `a`, and
/// `program.tree<h>_<a>` the tree over 16 of the trees one level down, the first of them at `a`.
/// Every definition is small: Lean elaborates many small definitions far faster than one large
/// one. Instructions must have strictly increasing addresses.
fn program(source: &mut String, instructions: &[Instruction]) -> std::fmt::Result {
    if instructions.is_empty() {
        return writeln!(source, "def program : Rivet.Program := .leaf []");
    }
    writeln!(source)?;
    let mut trees = Vec::new();
    for leaf in instructions.chunks(16) {
        let name = format!("program.leaf_{:x}", leaf[0].address);
        writeln!(source, "def {name} : Rivet.Program := .leaf [")?;
        for (index, instruction) in leaf.iter().enumerate() {
            writeln!(
                source,
                "  {{ address := {:#x}#64, length := {}, op := {} }}{}",
                instruction.address,
                instruction.length,
                operation(&instruction.op),
                if index + 1 < leaf.len() { "," } else { "]" }
            )?;
        }
        trees.push((leaf[0].address, name));
    }
    let mut height = 1;
    while trees.len() > 16 {
        let mut level = Vec::new();
        for group in trees.chunks(16) {
            let name = format!("program.tree{height}_{:x}", group[0].0);
            writeln!(source, "def {name} : Rivet.Program := {}", branches(group))?;
            level.push((group[0].0, name));
        }
        trees = level;
        height += 1;
    }
    writeln!(
        source,
        "def program : Rivet.Program := {}",
        branches(&trees)
    )
}

/// A balanced tree over `trees`, each given as its first address and its name.
fn branches(trees: &[(u64, String)]) -> String {
    if let [(_, name)] = trees {
        return name.clone();
    }
    let (left, right) = trees.split_at(trees.len() / 2);
    format!(
        "(.branch {:#x}#64 {} {})",
        right[0].0,
        branches(left),
        branches(right)
    )
}

fn name(value: impl std::fmt::Debug) -> String {
    format!(".{value:?}").to_ascii_lowercase()
}

fn address(value: &Address) -> String {
    let optional = |register| match register {
        Some(register) => format!("some {}", name(register)),
        None => "none".into(),
    };
    format!(
        "{{ base := {}, index := {}, scale := {}, displacement := ({}) }}",
        optional(value.base),
        optional(value.index),
        name(value.scale),
        value.displacement
    )
}

fn operand(value: &Operand) -> String {
    match value {
        Operand::Reg8 { register } => format!("(.reg8 {})", name(register)),
        Operand::Reg16 { register } => format!("(.reg16 {})", name(register)),
        Operand::Reg32 { register } => format!("(.reg32 {})", name(register)),
        Operand::Reg64 { register } => format!("(.reg64 {})", name(register)),
        Operand::Memory {
            width,
            address: value,
        } => format!("(.memory {} {})", name(width), address(value)),
        Operand::Immediate { value } => format!("(.immediate ({value}))"),
    }
}

fn condition(value: rivet_import::program::Condition) -> &'static str {
    use rivet_import::program::Condition::*;
    match value {
        Equal => ".equal",
        NotEqual => ".notEqual",
        Below => ".below",
        AboveOrEqual => ".aboveOrEqual",
        BelowOrEqual => ".belowOrEqual",
        Above => ".above",
        Sign => ".sign",
        Less => ".less",
        GreaterOrEqual => ".greaterOrEqual",
        LessOrEqual => ".lessOrEqual",
        Greater => ".greater",
    }
}

fn operation(value: &Operation) -> String {
    use Operation::*;
    match value {
        Nop => ".nop".into(),
        Binary {
            operation,
            destination,
            source,
        } => format!(
            ".binary {} {} {}",
            name(operation),
            operand(destination),
            operand(source)
        ),
        Mov {
            destination,
            source,
        } => format!(".mov {} {}", operand(destination), operand(source)),
        Lea {
            destination,
            source,
        } => format!(".lea {} {}", operand(destination), address(source)),
        Movzx {
            destination,
            source,
        } => format!(".movzx {} {}", name(destination), operand(source)),
        Movsxd {
            destination,
            source,
        } => format!(".movsxd {} {}", name(destination), operand(source)),
        Jmp { target } => format!(".jmp {target:#x}#64"),
        Jcc {
            condition: value,
            target,
        } => format!(".jcc {} {target:#x}#64", condition(*value)),
        Setcc {
            condition: value,
            destination,
        } => format!(".setcc {} {}", condition(*value), operand(destination)),
        Cmovcc {
            condition: value,
            destination,
            source,
        } => format!(
            ".cmovcc {} {} {}",
            condition(*value),
            operand(destination),
            operand(source)
        ),
        Inc { destination } => format!(".inc {}", operand(destination)),
        Dec { destination } => format!(".dec {}", operand(destination)),
        Ret => ".ret".into(),
        Call { target } => format!(".call {target:#x}#64"),
        Not { destination } => format!(".not {}", operand(destination)),
        Imul {
            destination,
            source,
            immediate,
        } => format!(
            ".imul {} {} {}",
            operand(destination),
            operand(source),
            immediate.map_or("none".into(), |value| format!("(some ({value}))"))
        ),
        Mul { source } => format!(".mul {}", name(source)),
        Tzcnt {
            destination,
            source,
        } => format!(".tzcnt {} {}", operand(destination), operand(source)),
        Shift {
            operation,
            destination,
            count,
        } => format!(
            ".shift {} {} {count}",
            name(operation),
            operand(destination)
        ),
        LoadXmm {
            operation,
            destination,
            source,
        } => format!(
            ".loadXmm {} {} {}",
            name(operation),
            name(destination),
            address(source)
        ),
        StoreXmm {
            operation,
            destination,
            source,
        } => format!(
            ".storeXmm {} {} {}",
            name(operation),
            address(destination),
            name(source)
        ),
        Movd {
            destination,
            source,
        } => format!(".movd {} {}", name(destination), name(source)),
        Pshufd {
            destination,
            source,
            order,
        } => format!(".pshufd {} {} {order}", name(destination), name(source)),
        Push { source } => format!(".push {}", name(source)),
        Pop { destination } => format!(".pop {}", name(destination)),
        Syscall => ".syscall".into(),
    }
}
