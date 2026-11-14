//! Prepare the common initial state before either runner executes.
use crate::{
    case::{Case, ExecutionInput, REGISTERS},
    register::Register64::Rsp,
};
use anyhow::{Context, Result, ensure};
use iced_x86::{Decoder, DecoderOptions, Mnemonic, OpKind, Register};
use memmap2::{Mmap, MmapMut};
use nix::{
    sys::mman::{ProtFlags, mprotect},
    unistd::{SysconfVar, sysconf},
};
use std::ptr::NonNull;

// Own the native allocations for as long as execution needs their addresses.
pub struct NativeMemory {
    pub code: Mmap,
    pub offsets: Vec<u64>,
    data: MmapMut,
}

pub fn prepare(case: &Case) -> Result<(ExecutionInput, NativeMemory)> {
    ensure!(
        !case.code.is_empty() && !case.data.is_empty(),
        "empty replay code or data"
    );
    let bytes = &case.code;
    let offsets = case.offsets.clone();
    let mut code = MmapMut::map_anon(bytes.len())?;
    code.copy_from_slice(bytes);
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
    let instructions: Vec<_> = Decoder::new(64, bytes, DecoderOptions::NONE)
        .into_iter()
        .collect();
    let register_index = |register| {
        REGISTERS
            .iter()
            .position(|&value| Register::from(value) == register)
    };
    for instruction in &instructions {
        if instruction.mnemonic() == Mnemonic::Lea
            || !instruction.op_kinds().any(|kind| kind == OpKind::Memory)
        {
            continue;
        }
        let index = register_index(instruction.memory_index());
        if let Some(index) = index {
            values[index] = case.registers[index] % 16;
        }
        if let Some(base) = register_index(instruction.memory_base()) {
            values[base] = data_pointer + case.registers[base] % 16;
        } else if let Some(index) = index {
            values[index] = data_pointer / instruction.memory_index_scale() as u64;
        }
    }
    if let [instruction] = instructions.as_slice()
        && matches!(instruction.mnemonic(), Mnemonic::Push | Mnemonic::Pop)
    {
        let slot = data_pointer + case.registers[Rsp as usize] % 16;
        values[Rsp as usize] = slot
            + if instruction.mnemonic() == Mnemonic::Push {
                8
            } else {
                0
            };
    }
    if instructions[0].mnemonic() == Mnemonic::Ret && case.fault_memory {
        values[Rsp as usize] = guard;
    }
    if instructions[0].mnemonic() == Mnemonic::Call && case.fault_memory {
        // Exercise CALL's stack write at the guard or read-only data boundary.
        values[Rsp as usize] = if case.read_only_data {
            base + 8
        } else {
            guard + 8
        };
    }
    let input = ExecutionInput {
        program: rivet_import::decode(&memory.code, memory.code.as_ptr() as u64)?,
        stop_address: continuation,
        registers: values,
        xmm_registers: case.xmm_registers,
        sign_flag: case.sign_flag,
        zero_flag: case.zero_flag,
        carry_flag: case.carry_flag,
        overflow_flag: case.overflow_flag,
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
