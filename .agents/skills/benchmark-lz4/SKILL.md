---
name: benchmark-lz4
description: Run a round of the LZ4 termination benchmark for Rivet (AI agents each prove that a compiled LZ4_decompress_safe always returns) on the machines and models the person names, then save, read and write up the results. Use when asked to benchmark LZ4, run an LZ4 eval or round, or kick off a benchmark in this repository.
---

# Running an LZ4 benchmark

How to run one round of the LZ4 termination benchmark end to end: package, launch, wait, save, read,
write up. A request looks like "benchmark lz4 on <machines> with <models>". The latest round under `evals/`
is the template: copy its folder and change what this file says to change. If something here disagrees with
the latest round's files, the files win; fix this skill.

## What it measures

Independent AI agents each prove `image_termination : Termination` for a compiled `LZ4_decompress_safe`
(709 instructions) using Rivet as it is on `main`. The goal is an API and docs smooth enough that an agent
does this in under an hour. Each round tests the library changes since the previous one.

## What the request decides

- **Machines.** Run the whole set of attempts once on each machine named, under one coordinator per
  machine. With no machine named, use this one. Find each machine's environment and project ids with your
  orchestration tools (for example `t3_environment_links`); do not assume them from an earlier round.
- **Models.** Use the models named, with the same settings on every machine. For each, find its
  `providerInstanceId`, model id and options with `orchestrator_capabilities` on every machine it will run
  on; a model missing anywhere is reported before launch, never substituted. Use high reasoning effort
  unless told otherwise (`effort: "high"` for Claude models, `reasoningEffort: "high"` for Codex models),
  and turn fast modes off. If no models are named, ask, offering the previous round's list.

An attempt's label is its model's short name; saved attempts are `<label>-<machine>`.

## Before launching

- Every machine must be reachable from yours. If delegation to a machine fails, find out why and fix it
  or report it; do not launch on the others alone without asking.
- A machine may be unable to message you back. Its coordinator then reports in its own log and replies,
  and you read its thread; its brief must say so.
- Fetch and build from `origin/main`, not a local `main`. If plain `git fetch` has no credentials, use
  `git -c credential.helper= -c credential.helper='!gh auth git-credential' fetch origin`.
- Each machine needs the `rivet.slice` systemd slice capped at 100 GB with no swap. The coordinator checks
  and sets it. Each attempt gets 16 GB through `lz4-termination/memrun`.

## 1. Package

The package is `lz4-termination/` on a branch `lz4-run-N`. It holds `TASK.txt`, `Lz4Termination/Spec.lean`
(the frozen goal), `Lz4Image.lean` (the imported program), `memrun`, `manifest.json` and `SHA256SUMS`.

    git switch -c lz4-run-N origin/main
    git checkout <previous package commit> -- lz4-termination

- Update `manifest.json`'s `rivet_revision` to `origin/main`'s full SHA.
- Regenerate `Lz4Image.lean` only if the importer changed:
  `cargo run -p rivet-import -- lz4.elf --function LZ4_decompress_safe --namespace Lz4Image`. Check that the
  instructions are unchanged and update `imported_image_sha256`.
- Change `Spec.lean` or `TASK.txt` only if the library change requires it, and record why.
- Regenerate the checksums: `cd lz4-termination && sha256sum TASK.txt manifest.json Lz4Image.lean
  Lz4Termination.lean Lz4Termination/Spec.lean Check.lean lakefile.toml lake-manifest.json lean-toolchain
  memrun > SHA256SUMS`.
- Build it with `./memrun lake build` from `lz4-termination`.
- Commit ("Add the LZ4 termination task package for run N") and push the branch, so that other machines can
  fetch it.

Leave your own checkout on `lz4-run-N`; your machine's coordinator checks `HEAD` there.

## 2. Round folder and tools

Make `evals/<date>-lz4-run-N/` (keep `evals/` out of git, e.g. through `.git/info/exclude`).

- `prior/`: the last two rounds' `FINDINGS.md`, as `FINDINGS-runK.md`.
- `tools/`: copy from the previous round and replace the old round number, branch name and package SHA
  everywhere.
  - `coordinator-<machine>.txt`: one brief per machine, from the previous round's. Fill in:
    - the machine's name;
    - the model table;
    - how it reports: messaging your thread (give your thread and environment ids) or, if it can't reach
      you, its log and replies;
    - which branch its checkout is on now.
  - `ATTEMPT_PROMPT.txt`, `RESUME_MESSAGE.txt`: unchanged between rounds unless the owner asks.
  - `verifyN.sh`: also embedded at the end of each brief; keep them in sync.
  - `save.sh`, `digest.py`, `stats.py`: saving and condensing transcripts.
  - `ANALYSIS_BRIEF.md`: rewritten each round, see step 5.
- `LAUNCH.md`: settings, what changed since the last round, coordinator ids, and an event log.

## 3. Launch

One coordinator per machine, Sonnet at high effort, started with `delegate_task`:
- role general, mode async, isolation shared;
- on that machine's environment and project;
- titled "LZ4 run N coordinator (<machine>)".

It runs its attempts as worktree children, sends early stoppers back to work, and verifies finished
attempts.

What to give it:
- **A coordinator on your machine** gets: "Your full instructions are in <round>/tools/coordinator-<machine>.txt.
  Read that file in full now (with `command cat`, since `cat` may be aliased) and follow it exactly."
- **A coordinator elsewhere** gets its whole brief inline, since it can't read your files.

The briefs already encode these rules:
- never help an attempt;
- a first hand-back is always resumed;
- a resumed run that changed nothing, a provider problem, or a claimed defect is reported, not resumed;
- at most 15 resumes per attempt;
- an attempt is verified by:
  - a clean rebuild;
  - `Check.lean` showing only `propext`, `Classical.choice` and `Quot.sound`;
  - no library changes;
  - no forbidden constructs, `bv_decide` and `native_decide` included.

Record each coordinator's task id and thread in `LAUNCH.md`.

## 4. While it runs

- Coordinators that can reach you message your thread as attempts finish. Read the others' threads and
  their `local/runN/coordinator-<machine>.md`.
- Log every stop, resume and verification in `LAUNCH.md`.
- Confirm commit SHAs from git before quoting them; coordinators have garbled SHAs in messages.
- If the owner cancels a model, tell every coordinator.
- Times are wall-clock minutes from launch to the last commit. Subtract outages, such as a server restart
  that froze attempts, and say so.

## 5. Save and read

1. **Your machine:** for each finished attempt, `bash <round>/tools/save.sh <label>-<machine> <worktree-id>`,
   with the worktree id from the coordinator's log. Check each printed line for a non-empty transcript and a
   digest with the expected time span. Copy `local/runN/verify-logs/<label>.txt` to
   `<round>/verification-logs/<label>-<machine>.txt`. `save.sh` assumes T3's worktree directory and Claude's
   and Codex's session folders; fix the paths if a machine keeps them elsewhere.
2. **Other machines:** push a temporary branch `runN-kit` holding `tools/` and `prior/`. Then delegate to each
   machine (Sonnet, effort high) a task that:
   - fetches the kit and unpacks it into the round folder;
   - extracts the package into `package/`;
   - confirms each attempt's HEAD from git, not from the log;
   - runs `save.sh` for each attempt;
   - copies the verify logs and the coordinator log.

   Delete `runN-kit` from origin afterwards.
3. **Analysis brief:** rewrite `tools/ANALYSIS_BRIEF.md` for this round. It must cover:
   - what changed in the library since last round, and what that change was meant to fix;
   - the results table;
   - the questions this round must answer.

   Keep the fixed parts:
   - read the whole digest;
   - give evidence with timestamps;
   - list stalls over a minute;
   - say which abstractions the agent built;
   - give the top five changes with minutes saved.

   The owner cares most about long stalls, wants API changes over docs, and dislikes piles of small
   bridging lemmas.
4. **Readers:** one per attempt, on the machine that holds it. Use a strong model at high effort (rounds so
   far used `gpt-6.1-sol`, `reasoningEffort` high, `serviceTier` ultrafast), role research, writing
   `attempts/<label>/analysis.md`. Add a per-attempt extra question when an attempt is unusual.
5. **Bring other machines' results back:** if the machines share no filesystem, have each machine tar
   `attempts`, `verification-logs` and its coordinator log. It sends the archive with
   `uvx --from magic-wormhole wormhole send --code-length 4 <file>` in the background and posts the code and
   sha256. Receive with `uvx --from magic-wormhole wormhole receive --accept-file <code>`, check the sha256,
   and unpack into the round folder.

## 6. Write up

- `FINDINGS.md`:
  - the short version;
  - results, with minutes against the previous round on the same machine;
  - whether this round's change did its job;
  - what still hurt;
  - what the readers ask for, counted;
  - recommended next changes;
  - notes on the run.

  Mark readers' estimates as estimates.
- `README.md`: one table of all attempts (model, machine, minutes, early stops, proof lines, clean rebuild,
  head), plus the folder layout.
- Clean up:
  - the temporary kit branch;
  - scratch worktrees;
  - leftover scratch files in `local/`.

  Leave the attempts' worktrees in place.
- Report to the owner:
  - the results table;
  - the verdict on this round's change;
  - the top recommendations.
