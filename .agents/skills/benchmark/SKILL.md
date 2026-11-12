---
name: benchmark
description: Use when asked to benchmark, run a benchmark, eval or round of a task, or run attempts at a task on machines with models.
---

# Running a benchmark round

Agents each attempt a proof task with Rivet's current `main`. The request names the task, machines,
attempt models and coordinator model; ask about anything missing. The task's latest round in
`evals/<date>-<task>-run-N/` is the template, and its files win over this skill.

1. **Check.** Look up each machine's ids and each model's settings with your orchestration tools; report
   anything unavailable, never substitute. Use high effort, no fast mode, the same settings everywhere.
2. **Package.** Make branch `<task>-run-N` from `origin/main` with the previous package. Update its
   manifest's revision and `SHA256SUMS`; touch the spec only if forced. Build it, push it, and stay on it.
3. **Folder.** Copy the previous round's `tools/`, updating round, branch, package SHA, machines and
   models in each coordinator brief. Add `prior/` (last two findings) and `LAUNCH.md`.
4. **Launch.** Start one coordinator per machine, giving it its brief (inline if remote). Never stop your
   own thread while the round runs: that stops every attempt.
5. **Watch.** Log stops and verifications in `LAUNCH.md` and confirm SHAs from git. Resume outages
   without counting them. Time is launch to last commit, minus outages.
6. **Read.** Save attempts with `tools/save.sh`, using a temporary kit branch on remote machines. Rewrite
   `ANALYSIS_BRIEF.md`, put one reader on each attempt, and bring remote results back with magic-wormhole.
7. **Write up.** Put results against the last round, whether the change worked, and next changes in
   `FINDINGS.md`, and the attempts table in `README.md`. Clean up temporary branches, then report. The
   owner cares most about long stalls, prefers API changes to docs, and dislikes piles of small lemmas.
