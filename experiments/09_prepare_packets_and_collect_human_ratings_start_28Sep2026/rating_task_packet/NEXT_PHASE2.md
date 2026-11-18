# Phase 2 (next 30 files): rate inside the Lean project

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/rating_task_packet/NEXT_PHASE2.md>

**TLDR:** DRAFT, not sent (Brando, 11-18-2026). For phase 2, raters open the same 25 task folders as a Lean project, so hovering any name shows exactly which definition it is (for example which `List`, or that a helper is not a vacuous or cheating stand-in). Setup downloads prebuilt Mathlib; nothing large is compiled. Phase 1 instructions and emails are unchanged.

**Why (Brando, 11-18-2026):** if people judge formal specification coverage, they should be able to check what each name in a theorem statement refers to. Otherwise a familiar name could point to a vacuous or cheating definition. The project also makes CI compile every file for them.

## Paste everything below this line into your coding agent (Claude Code, Codex, Cursor, …)

Set up the VeriBench rating packet as a Lean project on my computer so I can hover over names in the `.lean` files. Steps:

1. If `elan` (the Lean version manager) is not installed, install it:
   `curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none`
   then make sure `~/.elan/bin` is on `PATH`.
2. Clone the repository (or `git pull` if I already have it):
   `git clone https://github.com/brando90/trustworthy-theorem-judges.git`
3. `cd trustworthy-theorem-judges/experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/rating_task_packet/main_rating_task`
4. Run `lake exe cache get`. This downloads prebuilt Mathlib v4.22.0 (a few GB on disk, a few minutes). Do **not** build Mathlib from source; if this step fails, report the error instead.
5. Run `lake build` (builds two small VeriBench modules that one reference imports; seconds).
6. Check: `lake env lean task_01_heap_sort/gold_lean/reference.lean` should finish without `error:` lines.
7. Tell me to install the "Lean 4" extension in VS Code or Cursor and to open **this folder** (`main_rating_task`) as the workspace. Hover then works on every name.

Do not edit any file in the task folders. A few agent files have proof errors in Lean; that is expected and does not affect rating, which judges theorem statements, not proofs.

## For raters

- Same files and same personal Google Sheet as phase 1; only the place you open the files changes.
- Rate your next 30 files from the top of your Sheet, as before.
- Compile status of every file (Lean 4.22.0): [`support/LEAN_COMPILE_STATUS_MAIN_PACKET.json`](../support/LEAN_COMPILE_STATUS_MAIN_PACKET.json). On 11-18-2026: 112 of 125 compile, all 25 references included; 13 agent files have proof errors.

## Project facts (for maintainers)

- Project root: `rating_task_packet/main_rating_task/` (`lakefile.toml`, `lean-toolchain` = `leanprover/lean4:v4.22.0`, `lake-manifest.json` = VeriBench's Mathlib pins).
- `veribench/cs_set/*.lean`: two VeriBench modules imported by `task_17_heapsort_algorithm/gold_lean/reference.lean`, copied verbatim with hashes in [`veribench/SOURCE.md`](main_rating_task/veribench/SOURCE.md). The rating code is not added to VeriBench.
- Compile check: `python3 support/scripts/check_rating_lean_files.py`, which CI runs on every change (`.github/workflows/rating_lean_project.yml`).
