# Phase 2 rating setup: open the packet as a Lean project (hover works)

**TLDR:** For the next 30 files, clone the repository, let your agent run the setup below (it downloads prebuilt Mathlib, no recompiling), and open the repo folder in VS Code so hovering shows which `List` or other definition a name really is. The current email, sheets and rubric are unchanged.

*Draft 11-18-2026, not yet sent to anyone. The phase 1 email and instructions stay as they are; this is only the optional setup for phase 2.*

## Why

Rating coverage means checking that a name in the agent's theorem statement points at the real definition, not at a vacuous or look-alike one. In a plain folder of `.lean` files the editor cannot resolve names. As part of this repository the same files form one Lean 4.22.0 + Mathlib v4.22.0 project (`lakefile.toml` at the repository root), so hover, go-to-definition and `#print` show exactly what the checked environment sees. Continuous integration compiles the files, so the environment is known to work.

## Copy this whole block to your favorite coding agent

> Set up the VeriBench rating Lean project on my computer, then open it for me. Do not modify any packet file.
> 1. Install `git` and `elan` (the Lean version manager) if missing: `curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none`, then restart the shell so `lake` is on the PATH.
> 2. `git clone https://github.com/brando90/trustworthy-theorem-judges.git && cd trustworthy-theorem-judges`
> 3. Run `echo .lake/ >> .git/info/exclude` (keeps the 6 GB build folder out of Git without touching `.gitignore`), then `lake exe cache get`. This downloads prebuilt Mathlib (a few gigabytes, several minutes) instead of compiling it. Never run a plain `lake build` before this step.
> 4. Open the repository root folder in VS Code with the "Lean 4" extension installed (`code .`). Wait for the first file to finish elaborating once.
> 5. Open one candidate file, for example `experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/rating_task_packet/main_rating_task/task_01_heap_sort/agent_lean/agent_1.lean`, and confirm that hovering over a name shows its definition.
> 6. Tell me the Lean version (`lake env lean --version`) and anything that failed. Optional full check, about 10 to 20 minutes: `lake build RatingTask --keep-going`.

## How to use hover while rating

- Hover or press F12 on any name in `agent_lean/` or `gold_lean/` to see the real definition and its module (for example `List.sum` versus a locally defined `sum`).
- Add `#print axioms <theorem_name>` or `#check @<name>` at the bottom of a copy of the file if you want more; do not save changes to the packet files.
- A file that does not compile is still rated as before: score the statements, not the proofs.

## What stays the same

Rubric, 0-5 scale, personal sheet, deadline and the localized-AI-help rule are unchanged. Phase 1 raters can keep using the unzipped packet; the repository files are the same content.

## Known issues (11-18-2026)

- `main_rating_task/task_17_heapsort_algorithm/gold_lean/reference.lean` imports `veribench.cs_set.*` modules the packet does not ship, so it does not compile here. Open question: ship those modules or inline them before phase 2.
- 19 agent files (16 in the main packet, 3 in the warm-up) do not compile in this environment: some have unsolved proofs, and warm-up files import modules that do not exist in Mathlib v4.22.0 (`Mathlib.Data.Nat.GCD`, `Mathlib.Data.Nat.Gcd`, `Mathlib.Tactic.LibrarySearch`), so they were written for another Mathlib version. They are rating data, not CI failures; hover still works in the other files and in the files' own declarations where the file elaborates. The CI summary lists them (`support/scripts/check_lean_build.py`).
- The first full build on 11-18-2026 took about 20 minutes on a cloud machine with the prebuilt Mathlib cache; ordinary editing needs only `lake exe cache get` plus opening the file.
