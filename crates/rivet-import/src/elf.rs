use anyhow::{Context, Result, ensure};
use object::{
    Architecture, Object, ObjectKind, ObjectSymbol,
    elf::{
        PF_R, PF_W, PF_X, PT_DYNAMIC, PT_GNU_STACK, PT_INTERP, PT_LOAD, SHT_REL, SHT_RELA, SHT_RELR,
    },
    read::elf::{ElfFile64, FileHeader, ProgramHeader, SectionHeader},
};
use rivet_import::{Instruction, decode_one, program::Operation};
use std::collections::BTreeMap;

pub struct Image<'a> {
    pub entry: u64,
    pub program: Vec<Instruction>,
    pub segments: Vec<Segment<'a>>,
}

pub struct Segment<'a> {
    pub address: u64,
    pub start: u64,
    pub length: u128,
    pub size: u64,
    pub offset: u64,
    pub bytes: &'a [u8],
    pub writable: bool,
    pub executable: bool,
}

pub fn image<'a>(bytes: &'a [u8], roots: &[String]) -> Result<Image<'a>> {
    let file = ElfFile64::<object::Endianness>::parse(bytes).context("reading ELF64")?;
    let endian = file.endian();
    let eh = file.elf_header();
    ensure!(
        file.architecture() == Architecture::X86_64
            && file.is_little_endian()
            && file.kind() == ObjectKind::Executable
            && bytes[6] == 1
            && eh.e_version(endian) == 1,
        "expected a fixed-address, little-endian x86-64 ELF executable"
    );
    let header_size = u64::from(eh.e_phnum(endian)) * 56;
    ensure!(
        eh.e_phentsize(endian) == 56
            && header_size <= 4096
            && eh
                .e_phoff(endian)
                .checked_add(header_size)
                .is_some_and(|end| end <= bytes.len() as u64),
        "invalid program header table"
    );
    ensure!(
        !file
            .elf_section_table()
            .iter()
            .any(|header| matches!(header.sh_type(endian), SHT_REL | SHT_RELA | SHT_RELR)),
        "relocation records are not supported; link the executable without --emit-relocs"
    );
    let mut segments = Vec::new();
    let mut floor = 4096;
    let mut stack = false;
    for header in file.elf_program_headers() {
        let flags = header.p_flags(endian);
        match header.p_type(endian) {
            PT_DYNAMIC | PT_INTERP => anyhow::bail!("dynamic loading is not supported"),
            PT_GNU_STACK => {
                ensure!(flags & PF_X != PF_X, "executable stack is not supported");
                stack = true;
                continue;
            }
            PT_LOAD => {}
            _ => continue,
        }
        let address = header.p_vaddr(endian);
        let skip = address % 4096;
        let start = address - skip;
        let size = header.p_memsz(endian);
        let file_size = header.p_filesz(endian);
        let offset = header.p_offset(endian);
        let length = (u128::from(skip) + u128::from(size)).div_ceil(4096) * 4096;
        let end = u128::from(start) + length;
        let writable = flags & PF_W == PF_W;
        let executable = flags & PF_X == PF_X;
        ensure!(
            flags & PF_R == PF_R && !(writable && executable),
            "invalid PT_LOAD permissions at {address:#x}"
        );
        ensure!(
            size > 0 && (file_size == size || file_size < size && writable),
            "invalid PT_LOAD sizes at {address:#x}"
        );
        ensure!(
            offset % 4096 == skip && u128::from(start) >= floor && end <= 1u128 << 64,
            "invalid PT_LOAD page range at {address:#x}"
        );
        floor = end;
        ensure!(
            offset <= bytes.len() as u64,
            "segment offset outside ELF file"
        );
        let data = header
            .data(endian, bytes)
            .map_err(|()| anyhow::anyhow!("segment data outside ELF file"))?;
        segments.push(Segment {
            address,
            start,
            length,
            size,
            offset,
            bytes: data,
            writable,
            executable,
        });
    }
    ensure!(stack, "missing PT_GNU_STACK; link with -z noexecstack");
    let entry = file.entry();
    let mut pending = vec![entry];
    for root in roots {
        let address = if let Some(hex) = root.strip_prefix("0x") {
            u64::from_str_radix(hex, 16).with_context(|| format!("invalid root address {root}"))?
        } else {
            let mut matches = file
                .symbols()
                .filter(|s| !s.is_undefined() && s.name() == Ok(root.as_str()));
            let address = matches
                .next()
                .with_context(|| format!("undefined root symbol {root:?}"))?
                .address();
            ensure!(
                matches.all(|s| s.address() == address),
                "ambiguous root symbol {root:?}"
            );
            address
        };
        pending.push(address);
    }
    let program = reachable(&segments, pending)?;
    Ok(Image {
        entry,
        segments,
        program,
    })
}

fn reachable(segments: &[Segment<'_>], mut pending: Vec<u64>) -> Result<Vec<Instruction>> {
    let mut visited = BTreeMap::new();
    while let Some(address) = pending.pop() {
        if visited.contains_key(&address) {
            continue;
        }
        let bytes = segments
            .iter()
            .filter(|s| s.executable)
            .find_map(|s| {
                let offset = usize::try_from(address.checked_sub(s.address)?).ok()?;
                s.bytes.get(offset..).filter(|tail| !tail.is_empty())
            })
            .with_context(|| {
                format!("address {address:#x} is outside executable file-backed bytes")
            })?;
        let instruction = decode_one(bytes, address)?;
        if let Operation::Jmp { target }
        | Operation::Jcc { target, .. }
        | Operation::Call { target } = instruction.op
        {
            pending.push(target);
        }
        if !matches!(instruction.op, Operation::Ret | Operation::Jmp { .. })
            && instruction.length < bytes.len() as u64
        {
            pending.push(address + instruction.length);
        }
        visited.insert(address, instruction);
    }
    Ok(visited.into_values().collect())
}
