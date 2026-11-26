//! Linux/x86-64 execution only. Expected instruction behavior lives in Rivet.
use crate::{
    case::{ExecutionInput, Snapshot, Status},
    register::{register_values, set_registers, set_xmm_registers, xmm_values},
    setup::NativeMemory,
};
use anyhow::{Result, bail, ensure};
use nix::{
    errno::Errno,
    libc,
    sys::{
        ptrace,
        signal::{Signal, kill},
        wait::{WaitPidFlag, WaitStatus, waitpid},
    },
    unistd::{ForkResult, Pid, fork, getpid, getppid},
};
use std::{
    fs::File,
    os::unix::fs::FileExt,
    thread,
    time::{Duration, Instant},
};

/// Owns the traced child, including cleanup on any early return.
struct TracedChild {
    pid: Pid,
    // Whether waitpid has collected the child's exit status.
    reaped: bool,
}
impl TracedChild {
    fn start() -> Result<Self> {
        let parent = getpid();
        // SAFETY: the child only makes async-signal-safe syscalls, then stops/exits.
        let pid = match unsafe { fork()? } {
            ForkResult::Parent { child } => child,
            ForkResult::Child => unsafe {
                if nix::sys::prctl::set_pdeathsig(Signal::SIGKILL).is_err()
                    || getppid() != parent
                    || ptrace::traceme().is_err()
                {
                    libc::_exit(120);
                }
                let _ = kill(getpid(), Signal::SIGSTOP);
                libc::_exit(121);
            },
        };
        let mut child = Self { pid, reaped: false };
        ensure!(
            child.wait()? == WaitStatus::Stopped(pid, Signal::SIGSTOP),
            "child did not enter tracing stop; check ptrace permissions"
        );
        ptrace::setoptions(pid, ptrace::Options::PTRACE_O_EXITKILL)?;
        Ok(child)
    }

    fn wait(&mut self) -> Result<WaitStatus> {
        let deadline = Instant::now() + Duration::from_secs(2);
        loop {
            match waitpid(self.pid, Some(WaitPidFlag::WNOHANG)) {
                Ok(WaitStatus::StillAlive) => (),
                Ok(status) => {
                    self.reaped =
                        matches!(status, WaitStatus::Exited(..) | WaitStatus::Signaled(..));
                    return Ok(status);
                }
                Err(Errno::EINTR) => continue,
                Err(error) => {
                    self.reaped = error == Errno::ECHILD;
                    return Err(error.into());
                }
            }
            ensure!(Instant::now() < deadline, "native instruction timed out");
            thread::sleep(Duration::from_millis(1));
        }
    }
}

impl Drop for TracedChild {
    fn drop(&mut self) {
        if !self.reaped {
            let _ = kill(self.pid, Signal::SIGKILL);
            while waitpid(self.pid, None) == Err(Errno::EINTR) {}
        }
    }
}

fn snapshot(
    registers: &libc::user_regs_struct,
    floating_point: &libc::user_fpregs_struct,
    status: Status,
    process_memory: &File,
    memory_base: u64,
    memory_size: usize,
) -> Result<Snapshot> {
    let mut memory = vec![0; memory_size];
    process_memory.read_exact_at(&mut memory, memory_base)?;
    Ok(Snapshot {
        registers: register_values(registers),
        xmm_registers: xmm_values(floating_point),
        sign_flag: registers.eflags & (1 << 7) != 0,
        zero_flag: registers.eflags & (1 << 6) != 0,
        carry_flag: registers.eflags & 1 != 0,
        overflow_flag: registers.eflags & (1 << 11) != 0,
        status,
        memory,
    })
}

pub fn execute(input: &ExecutionInput, memory: &NativeMemory) -> Result<Vec<Snapshot>> {
    let code_base = input.code_base;
    let mut child = TracedChild::start()?;
    let process_memory = File::open(format!("/proc/{}/mem", child.pid))?;
    let mut registers = ptrace::getregs(child.pid)?;
    set_registers(&mut registers, input.registers);
    registers.rip = code_base;
    // Preserve OS-required flags; initialize SF/ZF/CF/OF and clear tracing/direction/resume bits.
    registers.eflags = (registers.eflags
        & !(1 | (1 << 6) | (1 << 7) | (1 << 8) | (1 << 10) | (1 << 11) | (1 << 16)))
        | ((input.overflow_flag as u64) << 11)
        | ((input.sign_flag as u64) << 7)
        | ((input.zero_flag as u64) << 6)
        | input.carry_flag as u64;
    ptrace::setregs(child.pid, registers)?;
    let mut floating_point = ptrace::getregset::<ptrace::regset::NT_PRFPREG>(child.pid)?;
    set_xmm_registers(&mut floating_point, input.xmm_registers);
    ptrace::setregset::<ptrace::regset::NT_PRFPREG>(child.pid, floating_point)?;
    registers = ptrace::getregs(child.pid)?;
    floating_point = ptrace::getregset::<ptrace::regset::NT_PRFPREG>(child.pid)?;
    let mut snapshots = vec![snapshot(
        &registers,
        &floating_point,
        Status::Running { address: code_base },
        &process_memory,
        input.memory_base,
        input.memory.len(),
    )?];
    for _ in 0..input.steps {
        ensure!(
            registers
                .rip
                .checked_sub(code_base)
                .is_some_and(
                    |offset| offset < memory.code.len() as u64 && memory.offsets.contains(&offset)
                ),
            "native execution left test code"
        );
        ptrace::step(child.pid, None)?;
        let WaitStatus::Stopped(_, signal) = child.wait()? else {
            bail!("native worker exited unexpectedly");
        };
        registers = ptrace::getregs(child.pid)?;
        floating_point = ptrace::getregset::<ptrace::regset::NT_PRFPREG>(child.pid)?;
        let status = match signal {
            Signal::SIGSEGV | Signal::SIGBUS => Status::Fault,
            Signal::SIGTRAP => {
                ensure!(
                    ptrace::getsiginfo(child.pid)?.si_code == libc::TRAP_TRACE,
                    "unexpected breakpoint instead of single-step stop"
                );
                if registers
                    .rip
                    .checked_sub(code_base)
                    .is_some_and(|offset| memory.offsets.contains(&offset))
                {
                    Status::Running {
                        address: registers.rip,
                    }
                } else {
                    Status::Outside {
                        address: registers.rip,
                    }
                }
            }
            _ => Status::Signal {
                number: signal as i32,
                address: registers.rip,
            },
        };
        let finished =
            !matches!(status, Status::Running { .. }) || registers.rip == input.stop_address;
        snapshots.push(snapshot(
            &registers,
            &floating_point,
            status,
            &process_memory,
            input.memory_base,
            input.memory.len(),
        )?);
        if finished {
            break;
        }
    }
    Ok(snapshots)
}
