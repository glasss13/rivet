//! Linux/x86-64 execution only. Expected instruction behavior lives in Rivet.
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
use serde::{Deserialize, Serialize, Serializer};
use std::{
    ffi::CStr,
    fmt::Write,
    fs::File,
    os::unix::fs::FileExt,
    thread,
    time::{Duration, Instant},
};

// Named as `Rivet.Access` names them.
#[allow(clippy::enum_variant_names)]
#[derive(Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum Access {
    ReadOnly,
    ReadExec,
    ReadWrite,
}
// A range of memory as it is mapped before the first instruction.
#[derive(Serialize)]
pub struct Mapping {
    pub base: u64,
    pub access: Access,
    #[serde(serialize_with = "hex")]
    pub bytes: Vec<u8>,
}
fn hex<S: Serializer>(bytes: &[u8], serializer: S) -> Result<S::Ok, S::Error> {
    let mut text = String::with_capacity(2 * bytes.len());
    for byte in bytes {
        write!(text, "{byte:02x}").unwrap();
    }
    serializer.serialize_str(&text)
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase", rename_all_fields = "camelCase")]
pub enum Status {
    Running { address: u64 },
    Exited { code: u8 },
    Fault,
    Signal { number: i32, address: u64 },
}
// A machine state as Linux and the model both report it. `writes` are the writable bytes the
// last step changed: with the mappings, that is all of memory.
#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Snapshot {
    pub registers: [u64; 16],
    pub xmm_registers: [[u32; 4]; 16],
    pub sign_flag: bool,
    pub zero_flag: bool,
    pub carry_flag: bool,
    pub overflow_flag: bool,
    pub status: Status,
    pub writes: Vec<(u64, u8)>,
}

// Four little-endian 32-bit words per XMM register, matching Linux's register set.
fn xmm_values(registers: &libc::user_fpregs_struct) -> [[u32; 4]; 16] {
    registers.xmm_space.as_chunks::<4>().0.try_into().unwrap()
}

fn register_values(registers: &libc::user_regs_struct) -> [u64; 16] {
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

/// Owns the traced child, including cleanup on any early return.
pub struct TracedChild {
    pub pid: Pid,
    // Whether waitpid has collected the child's exit status.
    reaped: bool,
}
impl TracedChild {
    /// Stop at the ELF entry point after Linux loads the program.
    pub fn start(program: &CStr) -> Result<Self> {
        let parent = getpid();
        let arguments = [program.as_ptr(), std::ptr::null()];
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
                libc::execv(program.as_ptr(), arguments.as_ptr());
                libc::_exit(121);
            },
        };
        let mut child = Self { pid, reaped: false };
        ensure!(
            child.wait()? == WaitStatus::Stopped(pid, Signal::SIGTRAP),
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

    fn snapshot(&self, signal: Signal, initial: bool, writes: Vec<(u64, u8)>) -> Result<Snapshot> {
        let registers = ptrace::getregs(self.pid)?;
        let floating_point = ptrace::getregset::<ptrace::regset::NT_PRFPREG>(self.pid)?;
        let status = match signal {
            Signal::SIGTRAP => {
                // Stepping over a real `syscall` stops with TRAP_BRKPT on this kernel; reject
                // `int3` (SI_KERNEL) and delivered SIGTRAP (SI_USER).
                let step_trap = initial
                    || matches!(
                        ptrace::getsiginfo(self.pid)?.si_code,
                        libc::TRAP_TRACE | libc::TRAP_BRKPT
                    );
                if step_trap {
                    Status::Running {
                        address: registers.rip,
                    }
                } else {
                    Status::Signal {
                        number: signal as i32,
                        address: registers.rip,
                    }
                }
            }
            Signal::SIGSEGV | Signal::SIGBUS => Status::Fault,
            _ => Status::Signal {
                number: signal as i32,
                address: registers.rip,
            },
        };
        Ok(Snapshot {
            registers: register_values(&registers),
            xmm_registers: xmm_values(&floating_point),
            sign_flag: registers.eflags & (1 << 7) != 0,
            zero_flag: registers.eflags & (1 << 6) != 0,
            carry_flag: registers.eflags & 1 != 0,
            overflow_flag: registers.eflags & (1 << 11) != 0,
            status,
            writes,
        })
    }

    /// The state now and after each instruction, until `stop` says so at a running state, the
    /// child is no longer running, or `steps` instructions have run.
    pub fn trace(
        &mut self,
        mappings: &[Mapping],
        steps: usize,
        mut stop: impl FnMut(&Snapshot) -> Result<bool>,
    ) -> Result<Vec<Snapshot>> {
        let memory = File::open(format!("/proc/{}/mem", self.pid))?;
        let mut writable: Vec<_> = mappings
            .iter()
            .filter(|mapping| mapping.access == Access::ReadWrite)
            .map(|mapping| (mapping.base, mapping.bytes.clone()))
            .collect();
        let mut snapshots = vec![self.snapshot(Signal::SIGTRAP, true, vec![])?];
        for _ in 0..steps {
            let last = snapshots.last().unwrap();
            if !matches!(last.status, Status::Running { .. }) || stop(last)? {
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
                    self.snapshot(signal, false, writes)?
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
