use crate::elf::Layout;
use anyhow::{Result, ensure};
use std::fmt::Write;

pub fn module(bytes: &[u8], layout: &Layout, namespace: &str) -> Result<String> {
    ensure!(
        !namespace.is_empty()
            && namespace.split('.').all(|part| !part.is_empty()
                && !part.chars().any(|c| c == '«' || c == '»' || c.is_control())),
        "invalid Lean namespace"
    );
    let namespace = namespace
        .split('.')
        .map(|part| format!("«{part}»"))
        .collect::<Vec<_>>()
        .join(".");
    let mut source =
        format!("module\npublic import Rivet\n@[expose] public section\nnamespace {namespace}\n");
    let mut pages = Vec::new();
    for (i, page) in bytes.chunks(4096).enumerate() {
        let name = format!("page_{i}");
        write!(source, "\ndef {name} : Nat := 0x")?;
        for byte in page.iter().rev() {
            write!(source, "{byte:02x}")?;
        }
        writeln!(source)?;
        pages.push(name);
    }
    writeln!(
        source,
        "\ndef file : Rivet.Exe := {{ size := {}, pages := [{}] }}",
        bytes.len(),
        pages.join(", ")
    )?;
    let mut names = Vec::new();
    for s in &layout.segments {
        let map_start = s.map_start();
        let suffix = format!("{:x}", map_start);
        let name = format!("segment_{suffix}");
        writeln!(
            source,
            "\nabbrev {name} : Rivet.Segment :=\n  {{ vaddr := {:#x}, memsz := {}, offset := {}, filesz := {},\n    writable := {}, executable := {} }}",
            s.vaddr, s.memsz, s.offset, s.filesz, s.writable, s.executable
        )?;
        writeln!(
            source,
            "abbrev region_{suffix} : Rivet.Region := Rivet.Region.root {:#x}#64 {} true {}",
            map_start,
            s.map_size(),
            s.writable
        )?;
        writeln!(
            source,
            "abbrev bytes_{suffix} : Rivet.Region := region_{suffix}.part {} {} (by rw [Rivet.Region.root_length]; decide)",
            s.page_offset(),
            s.memsz
        )?;
        names.push(name);
    }
    writeln!(
        source,
        "\ndef layout : Rivet.Layout := {{ entry := {:#x}, segments := [{}] }}",
        layout.entry,
        names.join(", ")
    )?;
    writeln!(
        source,
        "theorem layout_ok : file.layout = some layout := by decide +kernel"
    )?;
    writeln!(
        source,
        "def code : Rivet.Code := file.code layout\n\nend {namespace}"
    )?;
    Ok(source)
}
