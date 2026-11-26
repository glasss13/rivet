use nix::libc;

// Four little-endian 32-bit words per XMM register, matching Linux's register set.
pub(crate) fn xmm_values(registers: &libc::user_fpregs_struct) -> [[u32; 4]; 16] {
    registers.xmm_space.as_chunks::<4>().0.try_into().unwrap()
}

pub(crate) fn set_xmm_registers(registers: &mut libc::user_fpregs_struct, values: [[u32; 4]; 16]) {
    registers.xmm_space.copy_from_slice(values.as_flattened());
}

pub(crate) fn register_values(registers: &libc::user_regs_struct) -> [u64; 16] {
    [
        registers.rax,
        registers.rbx,
        registers.rcx,
        registers.rdx,
        registers.rsi,
        registers.rdi,
        registers.rbp,
        registers.rsp,
        registers.r8,
        registers.r9,
        registers.r10,
        registers.r11,
        registers.r12,
        registers.r13,
        registers.r14,
        registers.r15,
    ]
}

pub(crate) fn set_registers(registers: &mut libc::user_regs_struct, values: [u64; 16]) {
    [
        registers.rax,
        registers.rbx,
        registers.rcx,
        registers.rdx,
        registers.rsi,
        registers.rdi,
        registers.rbp,
        registers.rsp,
        registers.r8,
        registers.r9,
        registers.r10,
        registers.r11,
        registers.r12,
        registers.r13,
        registers.r14,
        registers.r15,
    ] = values;
}
