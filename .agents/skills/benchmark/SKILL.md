---
name: benchmark
description: Use when asked to benchmark, run a benchmark, eval or round of a task, or run attempts at a task on machines with models.
---

# Running a benchmark round

Independent agents each attempt a proof task with Rivet as it is on `main`; each round tests the library
changes since the last. The request names the task, the machines and the models. Rounds live in
`evals/<date>-<task>-run-N/`, and the task's latest round is the template: copy it, and where it and this
skill disagree, its files win. If the task, models or machines are unclear, ask.

**Setup per request.** One coordinator and one full set of attempts per machine (default: this one). Look
up each machine's ids and each model's provider, id and options with your orchestration tools on every
machine; report a missing model, never substitute. High reasoning effort, no fast mode, same settings
everywhere. Labels are model short names; saved attempts are `<label>-<machine>`.

## 1. Package

From `origin/main` (fetch with `gh auth git-credential` if plain fetch lacks credentials), make branch
`<task>-run-N` with the previous round's package directory. Set `manifest.json`'s `rivet_revision`;
re-import the program only if the importer changed; change the spec or `TASK.txt` only if the library
change forces it, and say why. Regenerate `SHA256SUMS`, build with `./memrun lake build`, commit, push,
and leave your checkout on that branch.

## 2. Round folder

Copy the previous round's `tools/`, replacing round number, branch and package SHA everywhere. Each
`coordinator-<machine>.txt` names its machine, the models, how it reports (to your thread, or in its own
log if it can't reach you) and its checkout's current branch; the verify script is embedded in it, so keep
the two in sync. Add `prior/` (last two `FINDINGS.md`) and `LAUNCH.md` (settings, changes, coordinator
ids, event log). Keep `evals/` out of git.

## 3. Launch

Per machine, `delegate_task` a Sonnet coordinator (high effort, async, shared isolation) on that machine:
locally, point it at its brief; elsewhere, paste the brief inline. The briefs already say: never help an
attempt; always resume a first hand-back; report rather than resume a resumed run that changed nothing,
a provider problem or a claimed defect; at most 15 resumes; verify by clean rebuild, only `propext`,
`Classical.choice`, `Quot.sound`, no library changes, no forbidden constructs. Each attempt runs in 16 GB,
each machine within a 100 GB `rivet.slice`.

Never stop your own thread during the round: it interrupts everything started from it.

## 4. While it runs

Log every stop, resume and verification in `LAUNCH.md`, and confirm SHAs from git. Read the threads of
coordinators that can't message you. If attempts are interrupted from outside, have coordinators resume
them with an outage message that doesn't count toward the 15. Time is minutes from launch to last
commit, minus outages.

## 5. Save and read

- Save each attempt with `tools/save.sh <label>-<machine> <worktree-id>` and copy its verify log. On other
  machines, push a temporary `runN-kit` branch with `tools/` and `prior/` and delegate the same steps there,
  with HEADs confirmed from git; delete the branch afterwards.
- Rewrite `tools/ANALYSIS_BRIEF.md`: what changed and why, the results, this round's questions, plus the
  fixed asks (whole digest, timestamped evidence, stalls over a minute, abstractions built, top five
  changes with minutes saved). The owner cares most about long stalls, prefers API changes to docs, and
  dislikes piles of small bridging lemmas.
- One reader per attempt, on its machine, writing `attempts/<label>/analysis.md` (a strong model at high
  effort; previous rounds used `gpt-6.1-sol`).
- Bring other machines' folders back with `uvx --from magic-wormhole wormhole send`/`receive`, checking the
  sha256.

## 6. Write up

`FINDINGS.md`: short version, results against the previous round, whether the change worked, what still
hurt, readers' requests counted, next changes, run notes; mark estimates. `README.md`: the attempts table
and layout. Delete temporary branches and scratch worktrees, keep attempt worktrees, and report the
table, the verdict and the top recommendations.
