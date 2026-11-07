use anyhow::{Context, Result, ensure};
use object::{
    Architecture, Object, ObjectKind, ObjectSymbol, SymbolKind,
    elf::{PF_X, PT_DYNAMIC, PT_INTERP, PT_LOAD, SHT_REL, SHT_RELA, SHT_RELR},
    read::elf::{ElfFile64, ProgramHeader, SectionHeader},
};

pub struct Function<'a> {
    pub address: u64,
    pub bytes: &'a [u8],
}

pub fn function<'a>(bytes: &'a [u8], name: &str) -> Result<Function<'a>> {
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
    let symbols: Vec<_> = file
        .symbols()
        .filter(|symbol| symbol.name() == Ok(name) && symbol.is_definition())
        .collect();
    ensure!(
        symbols.len() == 1,
        "expected one defined symbol named {name:?}"
    );
    let symbol = &symbols[0];
    ensure!(
        symbol.kind() == SymbolKind::Text && symbol.size() != 0,
        "function needs a nonzero-sized function symbol"
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
        "function must lie within one file-backed executable segment"
    );
    Ok(Function {
        address: symbol.address(),
        bytes: ranges[0],
    })
}
