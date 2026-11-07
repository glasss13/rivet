mod elf;
mod emit;

use anyhow::{Context, Result};
use clap::Parser;
use std::{fs, path::PathBuf};

#[derive(Parser)]
#[command(about = "Import one x86-64 ELF function into Rivet")]
struct Arguments {
    input: PathBuf,
    #[arg(long)]
    function: String,
    #[arg(long)]
    output: PathBuf,
    /// Lean namespace; defaults to the function name.
    #[arg(long)]
    namespace: Option<String>,
}

fn main() -> Result<()> {
    let args = Arguments::parse();
    let bytes = fs::read(&args.input).context("reading ELF file")?;
    let function = elf::function(&bytes, &args.function)?;
    let program = rivet_import::decode(function.bytes, function.address)?;
    let source = emit::module(
        &program,
        function.address,
        args.namespace.as_deref().unwrap_or(&args.function),
    )?;
    fs::write(&args.output, source).context("writing Lean module")?;
    Ok(())
}
