//! Linux/x86-64 execution only. Expected instruction behavior lives in Rivet.
use crate::{
    case::{Access, Case, Mapping, Snapshot, Status},
    register::{register_values, set_registers, set_xmm_registers, xmm_values},
    setup::Prepared,
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
    ffi::CStr,
    fs::File,
    os::unix::fs::FileExt,
    thread,
    time::{Duration, Instant},
};

/// Owns the traced child, including cleanup on any early return.
pub struct TracedChild {
    pub pid: Pid,
    // Whether waitpid has collected the child's exit status.
    reaped: bool,
}
impl TracedChild {
    /// A child stopped before its first instruction: at the entry of `program` as Linux loaded
    /// it, or without one, as a copy of this process.
    pub fn start(program: Option<&CStr>) -> Result<Self> {
        let parent = getpid();
        let arguments = program.map(|path| [path.as_ptr(), std::ptr::null()]);
        // SAFETY: the child only makes async-signal-safe syscalls, then stops/execs/exits.
        let pid = match unsafe { fork()? } {
            ForkResult::Parent { child } => child,
            ForkResult::Child => unsafe {
                if nix::sys::prctl::set_pdeathsig(Signal::SIGKILL).is_err()
                    || getppid() != parent
                    || ptrace::traceme().is_err()
                {
                    libc::_exit(120);
                }
                match &arguments {
                    // A traced execve stops with SIGTRAP once the new program is loaded.
                    Some(arguments) => {
                        libc::execv(arguments[0], arguments.as_ptr());
                    }
                    None => {
                        let _ = kill(getpid(), Signal::SIGSTOP);
                    }
                }
                libc::_exit(121);
            },
        };
        let mut child = Self { pid, reaped: false };
        let stop = if program.is_some() {
            Signal::SIGTRAP
        } else {
            Signal::SIGSTOP
        };
        ensure!(
            child.wait()? == WaitStatus::Stopped(pid, stop),
            "child did not enter tracing stop; check the program and ptrace permissions"
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
            thread::yield_now();
        }
    }

    fn snapshot(&self, signal: Signal, writes: Vec<(u64, u8)>) -> Result<Snapshot> {
        let registers = ptrace::getregs(self.pid)?;
        let floating_point = ptrace::getregset::<ptrace::regset::NT_PRFPREG>(self.pid)?;
        Ok(Snapshot {
            registers: register_values(&registers),
            xmm_registers: xmm_values(&floating_point),
            sign_flag: registers.eflags & (1 << 7) != 0,
            zero_flag: registers.eflags & (1 << 6) != 0,
            carry_flag: registers.eflags & 1 != 0,
            overflow_flag: registers.eflags & (1 << 11) != 0,
            status: match signal {
                Signal::SIGTRAP => Status::Running {
                    address: registers.rip,
                },
                Signal::SIGSEGV | Signal::SIGBUS => Status::Fault,
                _ => Status::Signal {
                    number: signal as i32,
                    address: registers.rip,
                },
            },
            writes,
        })
    }

    /// The state now and after each instruction, until `stop` says so at an address, the child
    /// is no longer running, or `steps` instructions have run.
    pub fn trace(
        &mut self,
        mappings: &[Mapping],
        steps: usize,
        stop: impl Fn(u64) -> Result<bool>,
    ) -> Result<Vec<Snapshot>> {
        let memory = File::open(format!("/proc/{}/mem", self.pid))?;
        let mut writable: Vec<_> = mappings
            .iter()
            .filter(|mapping| mapping.access == Access::ReadWrite)
            .map(|mapping| (mapping.base, mapping.bytes.clone()))
            .collect();
        let mut snapshots = vec![self.snapshot(Signal::SIGTRAP, vec![])?];
        for _ in 0..steps {
            let last = snapshots.last().unwrap();
            let Status::Running { address } = last.status else {
                break;
            };
            if stop(address)? {
                break;
            }
            ptrace::step(self.pid, None)?;
            let next = match self.wait()? {
                // `exit_group` ends the child inside the step, leaving no state to read.
                WaitStatus::Exited(_, code) => Snapshot {
                    status: Status::Exited { code: code as u8 },
                    writes: vec![],
                    ..last.clone()
                },
                WaitStatus::Stopped(_, signal) => {
                    let mut writes = vec![];
                    for (base, bytes) in &mut writable {
                        let mut read = vec![0; bytes.len()];
                        memory.read_exact_at(&mut read, *base)?;
                        if *bytes == read {
                            continue;
                        }
                        for (offset, (old, new)) in bytes.iter().zip(&read).enumerate() {
                            if old != new {
                                writes.push((*base + offset as u64, *new));
                            }
                        }
                        *bytes = read;
                    }
                    self.snapshot(signal, writes)?
                }
                status => bail!("unexpected wait status {status:?}"),
            };
            snapshots.push(next);
        }
        Ok(snapshots)
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

pub fn execute(case: &Case, prepared: &Prepared) -> Result<Vec<Snapshot>> {
    let code_base = prepared.mappings[0].base;
    let mut child = TracedChild::start(None)?;
    let mut registers = ptrace::getregs(child.pid)?;
    set_registers(&mut registers, prepared.registers);
    registers.rip = code_base;
    // Preserve OS-required flags; initialize SF/ZF/CF/OF and clear tracing/direction/resume bits.
    registers.eflags = (registers.eflags
        & !(1 | (1 << 6) | (1 << 7) | (1 << 8) | (1 << 10) | (1 << 11) | (1 << 16)))
        | ((case.overflow_flag as u64) << 11)
        | ((case.sign_flag as u64) << 7)
        | ((case.zero_flag as u64) << 6)
        | case.carry_flag as u64;
    ptrace::setregs(child.pid, registers)?;
    let mut floating_point = ptrace::getregset::<ptrace::regset::NT_PRFPREG>(child.pid)?;
    set_xmm_registers(&mut floating_point, case.xmm_registers);
    ptrace::setregset::<ptrace::regset::NT_PRFPREG>(child.pid, floating_point)?;
    child.trace(&prepared.mappings, case.steps, |address| {
        let offset = address.wrapping_sub(code_base);
        ensure!(
            case.offsets.contains(&offset),
            "native execution left test code"
        );
        Ok(offset == case.code.len() as u64)
    })
}
