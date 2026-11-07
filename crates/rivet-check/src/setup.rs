//! Prepare the common initial state before either runner executes.
use crate::{
    case::{Case, ExecutionInput, memory_address},
    register::Register64::Rsp,
};
use anyhow::{Context, Result, ensure};
use memmap2::{Mmap, MmapMut};
use nix::{
    sys::mman::{ProtFlags, mprotect},
    unistd::{SysconfVar, sysconf},
};
use rivet_import::program::Operation;
use std::ptr::NonNull;

// Own the native allocations for as long as execution needs their addresses.
pub struct NativeMemory {
    pub code: Mmap,
    pub offsets: Vec<u64>,
    data: MmapMut,
}

pub fn prepare(case: &Case) -> Result<(ExecutionInput, NativeMemory)> {
    let (bytes, offsets) = crate::encode::program(&case.program)?;
    let mut code = MmapMut::map_anon(bytes.len())?;
    code.copy_from_slice(&bytes);
    let code = code.make_exec()?;
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
    for address in case.program.iter().filter_map(memory_address) {
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
        program: rivet_import::decode(&memory.code, memory.code.as_ptr() as u64)?,
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
