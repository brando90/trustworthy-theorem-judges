# Heap-sort rating packet: Lean compilation check

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/support/lean_compile_heap_sort_11-18-2026/RESULTS.md>

**Status:** Checked on 11-18-2026. Three of four original files compile; `agent_3.lean` fails. No rating artifact was edited.

## Scope and environment

Requested directory: `experiments/23_brandos_judging/veribench_rating_packet_25_tasks_100_files/task_01_heap_sort/agent_lean/`.

Actual compiler execution, not a model reading. Pi coordinated local `lake env lean <absolute-file-path>` calls from `~/veribench/veribench_dataset/lean_src`, using its pinned Lean and Mathlib 4.22.0. No model judge was used. No differential testing (no DT), statement-coverage judgment, axiom audit, or human rating was performed.

- Lean: `4.22.0`, `arm64-apple-darwin23.6.0`, commit `ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05`.
- Mathlib: `79e94a093aff4a60fb1b1f92d9681e407124c2ca` (the checked-out revision matches the Lake manifest).
- Two compiler processes maximum; 180-second timeout per file. No file timed out.
- SHA-256 hashes before and after match for all four files; exact commands and hashes are in [results.json](results.json).

## Results

| File | Compiler exit code | Errors | Warnings | Result |
| --- | ---: | ---: | ---: | --- |
| `agent_1.lean` | 0 | 0 | 1 | Compiles |
| `agent_2.lean` | 0 | 0 | 0 | Compiles |
| `agent_3.lean` | 1 | 6 | 9 | Does not compile |
| `agent_4.lean` | 0 | 0 | 0 | Compiles |

The `agent_1.lean` warning is an unused `simp` argument (`add_zero`, line 216).

`agent_3.lean` fails inside the proof of `swapList_getElem!`:

- Line 229: failed to synthesize `GetElem? ℕ ℕ ... LT.lt`.
- Lines 228, 234, 235, 237, 238: unsolved goals involving indexed access and swap cases.

Full original compiler output: [agent_1.log](agent_1.log), [agent_2.log](agent_2.log), [agent_3.log](agent_3.log), [agent_4.log](agent_4.log).

## Interpretation and reproduction

A compilation success is not a statement-coverage verdict. The three compiling files contain existing `native_decide` uses; these were preserved, not introduced, and this check does not certify proofs under a policy excluding native evaluation. The failing file was not repaired or replaced, so the human-rating evidence remains unchanged. Any repair should be separately versioned rather than silently modifying the delivered packet.

Run `python3 experiments/23_brandos_judging/support/lean_compile_heap_sort/check.py` from the repository with the original packet at the requested path and the recorded VeriBench Lean environment installed. The script recompiles the four files and refreshes these logs and `results.json`.

**TLDR-end:** [human ratings: heap-sort compilation] Three files compile with the recorded Lean 4.22.0 environment; `agent_3.lean` does not. All four original file hashes are unchanged.

**Moved 11-18-2026:** Brando decided that the rating files live in the experiment 09 Lean project (`rating_task_packet/main_rating_task/`). The byte-identical `experiments/23_brandos_judging/` copy was removed and this check moved here. Paths inside the logs and `results.json` are kept as recorded.
