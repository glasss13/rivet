#[cfg(not(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu")))]
compile_error!("rivet-check currently requires x86-64 Linux with glibc");

mod case;
mod native;
mod process;
mod register;
mod setup;

use anyhow::{Context, Result, ensure};
use case::{Case, Mapping, Snapshot};
use clap::Parser;
use serde::{Deserialize, Serialize};
use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, ExitCode},
    time::Duration,
};
use subprocess::{Exec, Redirection};

#[derive(Parser)]
#[command(about = "Compare Rivet's interpreter with native x86-64 execution")]
struct Arguments {
    #[arg(long, default_value_t = 100)]
    cases: usize,
    #[arg(long, default_value_t = 42)]
    seed: u64,
    #[arg(long)]
    replay: Option<PathBuf>,
    /// Run this static ELF under Linux instead: check how it starts, then every instruction.
    #[arg(long)]
    exec: Option<PathBuf>,
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

fn check(model: &Path, case: &Case) -> Result<Option<String>> {
    let prepared = setup::prepare(case)?;
    let native = native::execute(case, &prepared)?;
    Ok(evaluate(model, &prepared.mappings, &native)?
        .map(|mismatch| format!("execution traces differ at step {}", mismatch.step)))
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

    if let Some(path) = args.exec {
        return Ok(match process::check(&model, &path, args.max_steps)? {
            Ok(outcome) => {
                println!("PASS: {outcome}");
                0
            }
            Err(reason) => {
                eprintln!("{reason}");
                1
            }
        });
    }

    if let Some(path) = args.replay {
        let case = serde_json::from_slice(&fs::read(path)?)?;
        if let Some(reason) = check(&model, &case)? {
            eprintln!("MISMATCH: {reason}");
            return Ok(1);
        }
        println!("Replay passed.");
        return Ok(0);
    }

    let mut generator = fastrand::Rng::with_seed(args.seed);
    for idx in 0..args.cases {
        let case = case::generate(&mut generator)?;
        if let Some(reason) =
            check(&model, &case).with_context(|| format!("case {idx}, seed {}", args.seed))?
        {
            eprintln!(
                "MISMATCH: case {idx}, seed {}: {reason}\n{}",
                args.seed,
                serde_json::to_string_pretty(&case)?
            );
            return Ok(1);
        }
    }
    println!("PASS: {} generated cases, seed {}.", args.cases, args.seed);
    Ok(0)
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
