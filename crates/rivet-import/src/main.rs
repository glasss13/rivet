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
    /// Lean namespace; defaults to the input filename stem.
    #[arg(long)]
    namespace: Option<String>,
}

fn main() -> Result<()> {
    let args = Arguments::parse();
    let bytes = fs::read(&args.input).context("reading ELF file")?;
    let layout = elf::layout(&bytes)?;
    let namespace = args
        .namespace
        .as_deref()
        .or_else(|| args.input.file_stem()?.to_str())
        .context("input has no UTF-8 stem, specify --namespace")?;
    let source = emit::module(&bytes, &layout, namespace)?;
    fs::write(&args.output, source).context("writing Lean module")?;
    Ok(())
}
