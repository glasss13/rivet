use anyhow::{Context, Result, ensure};
use object::{
    Architecture, Object, ObjectKind, ObjectSymbol, SymbolFlags, SymbolKind,
    elf::{
        PF_R, PF_W, PF_X, PT_DYNAMIC, PT_INTERP, PT_LOAD, SHT_REL, SHT_RELA, SHT_RELR, STT_FUNC,
    },
    read::elf::{ElfFile64, ProgramHeader, SectionHeader},
};

pub struct Function<'a> {
    pub address: u64,
    pub bytes: &'a [u8],
}

pub struct Image<'a> {
    pub entry: u64,
    pub functions: Vec<Function<'a>>,
    pub regions: Vec<MemoryRegion<'a>>,
}

pub struct MemoryRegion<'a> {
    pub address: u64,
    pub size: u64,
    pub bytes: &'a [u8],
    pub readable: bool,
    pub writable: bool,
}

pub fn image<'a>(bytes: &'a [u8], entry_name: &str) -> Result<Image<'a>> {
    let file = ElfFile64::<object::Endianness>::parse(bytes).context("reading ELF64")?;
    ensure!(
        file.architecture() == Architecture::X86_64
            && file.is_little_endian()
            && file.kind() == ObjectKind::Executable,
        "expected a fixed-address, little-endian x86-64 ELF executable"
    );
    let endian = file.endian();
    ensure!(
        !file
            .elf_program_headers()
            .iter()
            .any(|header| matches!(header.p_type(endian), PT_INTERP | PT_DYNAMIC)),
        "dynamic loading is not supported"
    );
    ensure!(
        !file
            .elf_section_table()
            .iter()
            .any(|header| matches!(header.sh_type(endian), SHT_REL | SHT_RELA | SHT_RELR)),
        "relocation records are not supported; link the executable without --emit-relocs"
    );
    let mut regions = Vec::new();
    for header in file.elf_program_headers() {
        if header.p_type(endian) != PT_LOAD {
            continue;
        }
        let address = header.p_vaddr(endian);
        let size = header.p_memsz(endian);
        let flags = header.p_flags(endian);
        ensure!(
            header.p_filesz(endian) <= size,
            "segment file size exceeds memory size"
        );
        address
            .checked_add(size)
            .context("segment address overflow")?;
        ensure!(
            flags & (PF_W | PF_X) != (PF_W | PF_X),
            "writable executable segments are not supported"
        );
        let data = header
            .data(endian, bytes)
            .map_err(|()| anyhow::anyhow!("segment data outside ELF file"))?;
        if size != 0 {
            regions.push(MemoryRegion {
                address,
                size,
                bytes: data,
                readable: flags & PF_R == PF_R,
                writable: flags & PF_W == PF_W,
            });
        }
    }
    regions.sort_by_key(|region| region.address);
    for pair in regions.windows(2) {
        ensure!(
            pair[0].address + pair[0].size <= pair[1].address,
            "overlapping loadable segments at {:#x} and {:#x}",
            pair[0].address,
            pair[1].address
        );
    }
    let symbols: Vec<_> = file
        .symbols()
        .filter(|symbol| !symbol.is_undefined() && symbol.kind() == SymbolKind::Text)
        .collect();
    let entries: Vec<_> = symbols
        .iter()
        .filter(|symbol| symbol.name() == Ok(entry_name))
        .collect();
    ensure!(
        entries.len() == 1,
        "expected one defined function named {entry_name:?}"
    );
    let entry = entries[0].address();
    let mut functions = Vec::new();
    for symbol in symbols {
        ensure!(
            matches!(symbol.flags(), SymbolFlags::Elf { st_info, .. } if st_info.st_type() == STT_FUNC),
            "indirect function resolvers are not supported"
        );
        ensure!(
            symbol.size() != 0,
            "function {:?} has no size",
            symbol.name()?
        );
        symbol
            .address()
            .checked_add(symbol.size())
            .context("function address overflow")?;
        let mut ranges = Vec::new();
        for header in file.elf_program_headers() {
            if header.p_type(endian) == PT_LOAD
                && header.p_flags(endian) & PF_X == PF_X
                && let Some(code) = header
                    .data_range(endian, bytes, symbol.address(), symbol.size())
                    .map_err(|()| anyhow::anyhow!("invalid executable segment"))?
            {
                ranges.push(code);
            }
        }
        ensure!(
            ranges.len() == 1,
            "function {:?} must lie within one file-backed executable segment",
            symbol.name()?
        );
        functions.push(Function {
            address: symbol.address(),
            bytes: ranges[0],
        });
    }
    functions.sort_by_key(|function| (function.address, function.bytes.len()));
    functions.dedup_by_key(|function| (function.address, function.bytes.len()));
    for pair in functions.windows(2) {
        ensure!(
            pair[0].address + pair[0].bytes.len() as u64 <= pair[1].address,
            "overlapping function ranges at {:#x} and {:#x}",
            pair[0].address,
            pair[1].address
        );
    }
    Ok(Image {
        entry,
        functions,
        regions,
    })
}
