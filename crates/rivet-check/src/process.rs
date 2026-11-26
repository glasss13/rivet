//! A real program under real Linux: `Rivet.Starts` at its entry, then every instruction.
use crate::{
    case::{Access, Mapping, Status},
    evaluate,
    native::TracedChild,
};
use anyhow::{Context, Result};
use iced_x86::{Decoder, DecoderOptions, Mnemonic};
use nix::{sys::ptrace, unistd::Pid};
use serde::Deserialize;
use std::{
    ffi::CString,
    fs::{self, File},
    os::unix::{ffi::OsStrExt, fs::FileExt},
    path::Path,
    process::{Command, Stdio},
};

// `Rivet.Layout`, as Lean's `Exe.layout` reads it from the file.
#[derive(Deserialize)]
struct Layout {
    entry: u64,
    segments: Vec<Segment>,
}
#[derive(Deserialize)]
struct Segment {
    vaddr: u64,
    memsz: u64,
    offset: u64,
    filesz: u64,
    writable: bool,
    executable: bool,
}

// A finding ends the check: what Linux did is not what Rivet says.
macro_rules! require {
    ($condition:expr, $($message:tt)+) => {
        if !$condition {
            return Ok(Err(format!($($message)+)));
        }
    };
}

/// Every field of `Rivet.Starts` against the child stopped at its entry. Returns the memory
/// `Starts` describes: each segment's pages and the stack.
fn starts(layout: &Layout, file: &[u8], pid: Pid) -> Result<Result<Vec<Mapping>, String>> {
    let registers = ptrace::getregs(pid)?;
    let memory = File::open(format!("/proc/{pid}/mem"))?;
    let read = |base: u64, length: u64| {
        let mut bytes = vec![0; length as usize];
        memory.read_exact_at(&mut bytes, base).map(|()| bytes)
    };
    let raw_maps = fs::read(format!("/proc/{pid}/maps"))?;
    let maps: Vec<_> = raw_maps
        .split(|&byte| byte == b'\n')
        .filter(|line| !line.is_empty())
        .map(|line| {
            let mut fields = line.splitn(3, |&byte| byte == b' ');
            let range = std::str::from_utf8(fields.next()?).ok()?;
            let permissions = std::str::from_utf8(fields.next()?).ok()?;
            if permissions.len() < 3 {
                return None;
            }
            let (start, end) = range.split_once('-')?;
            let address = |text| u64::from_str_radix(text, 16).ok();
            Some((address(start)?..address(end)?, permissions[..3].to_owned()))
        })
        .collect::<Option<_>>()
        .context("unreadable /proc maps")?;

    require!(
        registers.rip == layout.entry,
        "status: rip is {:#x}, the entry is {:#x}",
        registers.rip,
        layout.entry
    );
    let mut mappings = vec![];
    for segment in &layout.segments {
        let base = segment.vaddr / 4096 * 4096;
        let length = (segment.vaddr % 4096 + segment.memsz).div_ceil(4096) * 4096;
        let (access, expected) = match (segment.writable, segment.executable) {
            (true, _) => (Access::ReadWrite, "rw-"),
            (false, true) => (Access::ReadExec, "r-x"),
            (false, false) => (Access::ReadOnly, "r--"),
        };
        for page in (base..base + length).step_by(4096) {
            let found = maps
                .iter()
                .find(|(range, _)| range.contains(&page))
                .map_or("unmapped", |(_, permissions)| permissions);
            require!(
                found == expected,
                "access: the page at {page:#x} is {found}, its segment says {expected}"
            );
        }
        require!(
            segment
                .offset
                .checked_add(segment.filesz)
                .is_some_and(|end| end as usize <= file.len()),
            "same: segment at {:#x} extends past end of file",
            segment.vaddr
        );
        let bytes = read(base, length)?;
        for index in 0..segment.memsz {
            let address = segment.vaddr + index;
            let loaded = bytes[(address - base) as usize];
            let expected = if index < segment.filesz {
                file[(segment.offset + index) as usize]
            } else {
                0
            };
            require!(
                loaded == expected,
                "same: the byte at {address:#x} is {loaded:#04x}, the file says {expected:#04x}"
            );
        }
        mappings.push(Mapping {
            base,
            access,
            bytes,
        });
    }

    let rsp = registers.rsp;
    let Some((stack, permissions)) = maps.iter().find(|(range, _)| range.contains(&rsp)) else {
        return Ok(Err(format!("rsp: nothing is mapped at rsp, {rsp:#x}")));
    };
    require!(
        mappings.iter().all(|segment| stack.end <= segment.base
            || segment.base + segment.bytes.len() as u64 <= stack.start),
        "apart: the stack at {stack:#x?} overlaps a segment"
    );
    require!(
        permissions == "rw-",
        "stackWrites: the stack is {permissions}"
    );
    require!(
        stack.start % 4096 == 0 && stack.end % 4096 == 0,
        "stackPages: the stack is {stack:#x?}"
    );
    require!(rsp % 16 == 0, "aligned: rsp is {rsp:#x}");
    mappings.push(Mapping {
        base: stack.start,
        access: Access::ReadWrite,
        bytes: read(stack.start, stack.end - stack.start)?,
    });
    Ok(Ok(mappings))
}

/// `Ok` says what agreed; `Err` is the first thing that did not.
pub fn check(model: &Path, path: &Path, max_steps: usize) -> Result<Result<String, String>> {
    let file = fs::read(path)?;
    let layout = Command::new(model)
        .arg(path)
        .stderr(Stdio::inherit())
        .output()?;
    let layout: Option<Layout> =
        serde_json::from_slice(&layout.stdout).context("reading the layout from Lean")?;
    let Some(layout) = layout else {
        return Ok(Err(format!(
            "UNSUPPORTED: Exe.layout rejects {}",
            path.display()
        )));
    };
    let mut child = TracedChild::start(Some(&CString::new(path.as_os_str().as_bytes())?))?;
    let mappings = match starts(&layout, &file, child.pid)? {
        Ok(mappings) => mappings,
        Err(reason) => return Ok(Err(format!("MISMATCH: Starts.{reason}"))),
    };
    let exec_bytes = |address: u64| {
        mappings
            .iter()
            .filter(|mapping| mapping.access == Access::ReadExec)
            .find_map(|mapping| {
                mapping
                    .bytes
                    .get(address.checked_sub(mapping.base)? as usize..)
            })
    };
    let mut stopped_syscall: Option<(usize, u64, u64)> = None;
    let mut step_index = 0usize;
    let native = child.trace(&mappings, max_steps, |snapshot| {
        step_index += 1;
        let Status::Running { address } = snapshot.status else {
            return Ok(true);
        };
        // Never execute an unmodeled syscall natively; only unprefixed `exit_group` (231) is modeled.
        if let Some(bytes) = exec_bytes(address) {
            let decoded = Decoder::with_ip(64, bytes, address, DecoderOptions::NONE).decode();
            if decoded.mnemonic() == Mnemonic::Syscall
                && !(bytes.starts_with(&[0x0f, 0x05]) && snapshot.registers[0] == 231)
            {
                stopped_syscall = Some((step_index, snapshot.registers[0], address));
                return Ok(true);
            }
        }
        Ok(false)
    })?;
    let Some(mismatch) = evaluate(model, &mappings, &native)? else {
        if let Some((step, rax, address)) = stopped_syscall {
            return Ok(Err(format!(
                "UNSUPPORTED: step {step}: syscall {rax} at {address:#x}"
            )));
        }
        let steps = native.len() - 1;
        return Ok(match native[steps].status {
            Status::Running { .. } => Err(format!(
                "INCOMPLETE: Starts holds; {steps} steps agree (--max-steps {max_steps})"
            )),
            ref end => Ok(format!("Starts holds; {steps} steps agree, ending in {end:?}")),
        });
    };

    let step = mismatch.step;
    let [rax, ..] = native[step - 1].registers;
    let Status::Running { address } = native[step - 1].status else {
        unreachable!("tracing stops at the first state that is not running")
    };
    let instruction = exec_bytes(address)
        .map(|bytes| Decoder::with_ip(64, bytes, address, DecoderOptions::NONE).decode());
    let alone = mismatch.model.status == Status::Fault && native[step].status != Status::Fault;
    let (linux, model) = (
        serde_json::to_value(&native[step])?,
        serde_json::to_value(&mismatch.model)?,
    );
    let differences: String = linux
        .as_object()
        .into_iter()
        .flatten()
        .filter(|(field, value)| model[field.as_str()] != **value)
        .map(|(field, value)| {
            format!(
                "\n  {field}: Linux {value}, model {}",
                model[field.as_str()]
            )
        })
        .collect();
    Ok(Err(match instruction {
        Some(instruction) if alone && instruction.mnemonic() == Mnemonic::Syscall => {
            format!("UNSUPPORTED: step {step}: syscall {rax} at {address:#x}")
        }
        Some(instruction) if !mismatch.decoded => {
            format!("UNSUPPORTED: step {step}: instruction `{instruction}` at {address:#x}")
        }
        _ => format!(
            "MISMATCH: step {step} at {address:#x}{}{differences}",
            instruction.map_or(String::new(), |instruction| format!(" (`{instruction}`)")),
        ),
    }))
}
