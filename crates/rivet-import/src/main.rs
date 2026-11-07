mod elf;
mod emit;

use anyhow::{Context, Result, ensure};
use clap::Parser;
use rivet_import::program::Operation;
use std::{fs, path::PathBuf};

#[derive(Parser)]
#[command(about = "Import all defined x86-64 ELF functions into Rivet")]
struct Arguments {
    input: PathBuf,
    #[arg(long)]
    /// Function to use as the entry point; all defined functions are imported.
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
    let image = elf::image(&bytes, &args.function)?;
    let mut program = Vec::new();
    for function in image.functions {
        program.extend(rivet_import::decode(function.bytes, function.address)?);
    }
    for instruction in &program {
        if let Operation::Jmp { target }
        | Operation::Jcc { target, .. }
        | Operation::Call { target } = instruction.op
        {
            ensure!(
                program
                    .binary_search_by_key(&target, |instruction| instruction.address)
                    .is_ok(),
                "at {:#x}: target {target:#x} is not an imported instruction boundary",
                instruction.address
            );
        }
    }
    let source = emit::module(
        &program,
        image.entry,
        args.namespace.as_deref().unwrap_or(&args.function),
    )?;
    fs::write(&args.output, source).context("writing Lean module")?;
    Ok(())
}
