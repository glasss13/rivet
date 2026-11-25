mod elf;
mod emit;

use anyhow::{Context, Result};
use clap::Parser;
use std::{fs, path::PathBuf};

#[derive(Parser)]
#[command(about = "Import a static x86-64 ELF executable into Rivet")]
struct Arguments {
    input: PathBuf,
    #[arg(long)]
    output: PathBuf,
    #[arg(long)]
    namespace: String,
    /// Additional disassembly root (0x address or defined ELF symbol).
    #[arg(long)]
    root: Vec<String>,
}

fn main() -> Result<()> {
    let args = Arguments::parse();
    let bytes = fs::read(&args.input).context("reading ELF file")?;
    let image = elf::image(&bytes, &args.root)?;
    let source = emit::module(&bytes, &image, &args.namespace)?;
    fs::write(&args.output, source).context("writing Lean module")
}
