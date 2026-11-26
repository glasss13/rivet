#[cfg(not(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu")))]
compile_error!("rivet-check currently requires x86-64 Linux with glibc");

mod native;
mod process;

use anyhow::{Context, Result, ensure};
use clap::Parser;
use native::{Mapping, Snapshot};
use serde::{Deserialize, Serialize};
use std::{
    path::{Path, PathBuf},
    process::{Command, ExitCode},
    time::Duration,
};
use subprocess::{Exec, Redirection};

#[derive(Parser)]
#[command(about = "Compare Rivet's interpreter with native x86-64 execution")]
struct Arguments {
    /// Static x86-64 ELF executable to check.
    program: PathBuf,
    #[arg(long, default_value_t = 10_000)]
    max_steps: usize,
}

#[derive(Serialize)]
struct Request<'a> {
    mappings: &'a [Mapping],
    start: &'a Snapshot,
    steps: &'a [Snapshot],
}

// The first step whose state the model computes differently, and whether its instruction decoded.
#[derive(Deserialize)]
struct Mismatch {
    step: usize,
    model: Snapshot,
    decoded: bool,
}

fn evaluate(model: &Path, mappings: &[Mapping], native: &[Snapshot]) -> Result<Option<Mismatch>> {
    let request = Request {
        mappings,
        start: &native[0],
        steps: &native[1..],
    };
    let job = Exec::cmd(model)
        .stdin(serde_json::to_vec(&request)?)
        .stdout(Redirection::Pipe)
        .start()
        .context("starting Lean model")?;

    let process = job.processes[0].clone();
    // The model reads back every writable byte after every step.
    let deadline = Duration::from_secs(5) + Duration::from_millis(10) * native.len() as u32;
    let capture = job.capture_timeout(deadline);
    if capture.is_err() {
        let _ = process.kill();
    }
    let capture =
        capture.with_context(|| format!("evaluating Lean model ({deadline:?} deadline)"))?;
    ensure!(
        capture.exit_status.success(),
        "model exited with {}",
        capture.exit_status
    );
    serde_json::from_slice(&capture.stdout).context("invalid model response")
}

fn run(args: Arguments) -> Result<u8> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let model = root.join(".lake/build/bin/model");
    ensure!(
        Command::new("lake")
            .args(["build", "model"])
            .current_dir(root)
            .status()?
            .success(),
        "Lean model build failed"
    );

    Ok(
        match process::check(&model, &args.program, args.max_steps)? {
            Ok(outcome) => {
                println!("PASS: {outcome}");
                0
            }
            Err(reason) => {
                eprintln!("{reason}");
                1
            }
        },
    )
}

fn main() -> ExitCode {
    let code = match run(Arguments::parse()) {
        Ok(code) => code,
        Err(error) => {
            eprintln!("HARNESS ERROR: {error:#}");
            2
        }
    };
    ExitCode::from(code)
}
