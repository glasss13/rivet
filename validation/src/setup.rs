//! Prepare the common initial state before either runner executes.
use crate::{
    case::{Case, ExecutionInput, Operation},
    register::Register64::Rsp,
};
use anyhow::{Context, Result, ensure};
use memmap2::{Mmap, MmapMut};
use nix::{
    sys::mman::{ProtFlags, mprotect},
    unistd::{SysconfVar, sysconf},
};
use object::{Object, ObjectSection, ObjectSymbol};
use std::{fs, process::Command, ptr::NonNull};

// Own the native allocations for as long as execution needs their addresses.
pub struct NativeMemory {
    pub code: Mmap,
    pub offsets: Vec<u64>,
    data: MmapMut,
}

fn assemble(source: &str, instructions: usize) -> Result<(Mmap, Vec<u64>)> {
    let directory = tempfile::tempdir()?;
    let assembly = directory.path().join("case.s");
    let object_path = directory.path().join("case.o");
    fs::write(
        &assembly,
        format!(".intel_syntax noprefix\n.text\n{source}"),
    )?;
    let output = Command::new("as")
        .arg("--64")
        .arg(&assembly)
        .arg("-o")
        .arg(&object_path)
        .output()
        .context("starting GNU assembler")?;
    ensure!(
        output.status.success(),
        "assembler: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let bytes = fs::read(object_path)?;
    let object = object::File::parse(bytes.as_slice())?;
    let text = object
        .section_by_name(".text")
        .context("missing .text section")?;
    ensure!(
        text.relocations().next().is_none(),
        "unexpected code relocation"
    );
    let offsets: Vec<_> = (0..=instructions)
        .map(|index| {
            let name = if index == instructions {
                "rivet_end".into()
            } else {
                format!("rivet_instruction_{index}")
            };
            object
                .symbol_by_name(&name)
                .map(|symbol| symbol.address())
                .context("missing instruction boundary")
        })
        .collect::<Result<_>>()?;
    let bytes = text.data()?;
    ensure!(
        offsets[0] == 0 && offsets[instructions] == bytes.len() as u64,
        "invalid instruction boundaries"
    );
    let mut code = MmapMut::map_anon(bytes.len())?;
    code.copy_from_slice(bytes);
    Ok((code.make_exec()?, offsets))
}

pub fn prepare(case: &Case) -> Result<(ExecutionInput, NativeMemory)> {
    let source = case.assembly();
    let (code, offsets) = assemble(&source, case.program.len())?;
    let page = sysconf(SysconfVar::PAGE_SIZE)?.context("cannot determine page size")? as usize;
    ensure!(code.len() < page, "test code exceeds one page");
    let continuation = code.as_ptr() as u64 + code.len() as u64;
    let mut memory = NativeMemory {
        code,
        offsets,
        data: MmapMut::map_anon(page * 3)?,
    };
    for (index, byte) in memory.data[..page].iter_mut().enumerate() {
        *byte = case.data[index % case.data.len()];
    }
    let base = memory.data.as_ptr() as u64;
    let stack_offset = page + page / 2;
    memory.data[stack_offset..stack_offset + 8].copy_from_slice(&continuation.to_le_bytes());
    let memory_bytes = memory.data[..page * 2].to_vec();
    let guard = base + (page * 2) as u64;
    // SAFETY: page-aligned subrange of this owned mapping; no slices are accessed afterward.
    unsafe {
        mprotect(
            NonNull::new(guard as *mut _).unwrap(),
            page,
            ProtFlags::PROT_NONE,
        )?;
    }
    if case.read_only_data {
        // SAFETY: the first page is an aligned, owned data region, separate from the return stack.
        unsafe {
            mprotect(
                NonNull::new(base as *mut _).unwrap(),
                page,
                ProtFlags::PROT_READ,
            )?;
        }
    }
    let mut values = case.registers;
    values[Rsp as usize] = base + stack_offset as u64;
    // Include accesses starting just before the guard page, so wider accesses
    // can fault after their first byte. Other cases exercise unaligned data.
    let data_pointer = if case.fault_memory {
        guard - 8
    } else {
        base + 64
    };
    for address in case.program.iter().filter_map(Operation::memory_address) {
        if let Some(index) = address.index {
            values[index as usize] = case.registers[index as usize] % 16;
        }
        if let Some(register) = address.base {
            values[register as usize] = data_pointer + case.registers[register as usize] % 16;
        } else if let Some(index) = address.index {
            values[index as usize] = data_pointer / address.scale.value();
        }
    }
    if let [operation @ (Operation::Push { .. } | Operation::Pop { .. })] = case.program.as_slice()
    {
        // Place the accessed slot in data or across the guard, including unaligned RSP.
        let slot = data_pointer + case.registers[Rsp as usize] % 16;
        values[Rsp as usize] = slot
            + if matches!(operation, Operation::Push { .. }) {
                8
            } else {
                0
            };
    }
    if case.program[0] == Operation::Ret && case.fault_memory {
        values[Rsp as usize] = guard;
    }
    let input = ExecutionInput {
        program: case.program.clone(),
        registers: values,
        xmm_registers: case.xmm_registers,
        sign_flag: case.sign_flag,
        zero_flag: case.zero_flag,
        carry_flag: case.carry_flag,
        memory_base: base,
        writable_base: if case.read_only_data {
            base + page as u64
        } else {
            base
        },
        memory: memory_bytes,
        steps: case.steps,
    };
    Ok((input, memory))
}
