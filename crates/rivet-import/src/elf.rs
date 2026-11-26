use anyhow::{Result, ensure};

pub struct Segment {
    pub vaddr: u64,
    pub memsz: u64,
    pub offset: u64,
    pub filesz: u64,
    pub writable: bool,
    pub executable: bool,
}

impl Segment {
    pub fn map_start(&self) -> u64 {
        self.vaddr - (self.vaddr % 4096)
    }

    pub fn page_offset(&self) -> u64 {
        self.vaddr % 4096
    }

    pub fn map_size(&self) -> u128 {
        (u128::from(self.page_offset()) + u128::from(self.memsz)).next_multiple_of(4096)
    }
}

pub struct Layout {
    pub entry: u64,
    pub segments: Vec<Segment>,
}

pub fn layout(bytes: &[u8]) -> Result<Layout> {
    ensure!(bytes.len() >= 64, "truncated ELF header");
    let u16_at = |i: usize| u16::from_le_bytes(bytes[i..i + 2].try_into().unwrap());
    let u32_at = |i: usize| u32::from_le_bytes(bytes[i..i + 4].try_into().unwrap());
    let u64_at = |i: usize| u64::from_le_bytes(bytes[i..i + 8].try_into().unwrap());
    ensure!(
        &bytes[..7] == b"\x7fELF\x02\x01\x01"
            && u16_at(16) == 2
            && u16_at(18) == 62
            && u32_at(20) == 1,
        "expected a fixed-address little-endian x86-64 ELF64 executable"
    );
    let entry = u64_at(24);
    let table = u64_at(32);
    let count = usize::from(u16_at(56));
    ensure!(
        u16_at(54) == 56 && count * 56 <= 4096,
        "invalid program header size or count"
    );
    ensure!(
        u128::from(table) + (count * 56) as u128 <= bytes.len() as u128,
        "program headers outside file"
    );
    let mut segments = Vec::new();
    let mut floor = 4096u128;
    let mut stack = false;
    let mut entry_mapped = false;
    for index in 0..count {
        let i = table as usize + index * 56;
        let flags = u32_at(i + 4);
        let writable = flags & 2 != 0;
        let executable = flags & 1 != 0;
        match u32_at(i) {
            2 | 3 => anyhow::bail!("dynamic loading is unsupported"),
            0x6474e551 => {
                ensure!(!executable, "executable GNU stack");
                stack = true;
            }
            1 => {
                let offset = u64_at(i + 8);
                let vaddr = u64_at(i + 16);
                let filesz = u64_at(i + 32);
                let memsz = u64_at(i + 40);
                let page_offset = vaddr % 4096;
                let map_start = vaddr - page_offset;
                let map_size = (u128::from(page_offset) + u128::from(memsz)).next_multiple_of(4096);
                ensure!(
                    flags & 4 != 0 && !(writable && executable),
                    "invalid PT_LOAD permissions at {vaddr:#x}"
                );
                ensure!(
                    memsz > 0 && (filesz == memsz || (filesz < memsz && writable)),
                    "invalid PT_LOAD sizes at {vaddr:#x}"
                );
                ensure!(
                    u128::from(offset) + u128::from(filesz) <= bytes.len() as u128
                        && offset % 4096 == page_offset,
                    "invalid PT_LOAD file range or alignment at {vaddr:#x}"
                );
                ensure!(
                    floor <= u128::from(map_start),
                    "PT_LOAD pages overlap, descend, or include the null page"
                );
                floor = u128::from(map_start) + map_size;
                ensure!(floor <= 1u128 << 64, "PT_LOAD pages overflow address space");
                entry_mapped |=
                    executable && entry.checked_sub(vaddr).is_some_and(|n| n < filesz);
                segments.push(Segment {
                    vaddr,
                    memsz,
                    offset,
                    filesz,
                    writable,
                    executable,
                });
            }
            _ => {}
        }
    }
    ensure!(stack, "missing PT_GNU_STACK");
    ensure!(entry_mapped, "entry point outside executable file bytes");
    Ok(Layout { entry, segments })
}
