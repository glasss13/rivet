#[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
compile_error!("rivet-check currently requires x86-64 Linux");

mod case;
mod native;
mod operand;
mod register;
mod setup;

use anyhow::{Context, Result, ensure};
use case::{Case, ExecutionInput, Snapshot};
use clap::Parser;
use serde::Deserialize;
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
}

#[derive(Deserialize)]
#[serde(untagged)]
enum Response {
    Success { snapshots: Vec<Snapshot> },
    Error { error: String },
}

fn evaluate(model: &Path, request: &ExecutionInput) -> Result<Response> {
    let job = Exec::cmd(model)
        .stdin(serde_json::to_vec(request)?)
        .stdout(Redirection::Pipe)
        .start()
        .context("starting Lean model")?;

    let process = job.processes[0].clone();
    let capture = job.capture_timeout(Duration::from_secs(5));
    if capture.is_err() {
        let _ = process.kill();
    }
    let capture = capture.context("evaluating Lean model (five-second deadline)")?;
    ensure!(
        capture.exit_status.success(),
        "model exited with {}",
        capture.exit_status
    );
    serde_json::from_slice(&capture.stdout).context("invalid model response")
}

fn check(model: &Path, case: &Case) -> Result<Option<String>> {
    let (input, memory) = setup::prepare(case)?;
    let native = native::execute(&input, &memory)?;
    match evaluate(model, &input)? {
        Response::Success { snapshots } => {
            Ok((snapshots != native).then(|| "execution traces differ".into()))
        }
        Response::Error { error } => Ok(Some(format!("model rejected assembled case: {error}"))),
    }
}

fn run(args: Arguments) -> Result<u8> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let model = root.join(".lake/build/bin/model");
    println!("{:?}", model);
    ensure!(
        Command::new("lake")
            .args(["build", "model"])
            .current_dir(root)
            .status()?
            .success(),
        "Lean model build failed"
    );

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
        let case = case::generate(&mut generator);
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
