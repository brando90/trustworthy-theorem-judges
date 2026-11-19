# Experiment 23 results: do gamed or off-format Lean files score lower on VeriBench VB256?

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/23_do_gamed_or_off_format_lean_files_score_lower_on_veribench_vb256_start_18Nov2026/results.md>

**Status:** RUNNING (started 11-19-2026 15:05 PST)
**Last updated:** 11-19-2026 15:50 PST

Design and pre-registration: [README.md](README.md). VeriBench `veribench@1.3` task list (VB256 manifest), files at `brando90/veribench` `8b4a11010c`. Lean-checked: compile and kernel axiom audit; model reading: Claude Opus 5.5 judge. No differential testing; not the VeriBench prover.

| Phase | Status | Result so far |
| --- | --- | --- |
| 1. Import VB256 (256 gold + Python, hashes) | DONE | 256/256 found, none missing; manifest hash verified |
| 2. Smoke test of the checks on two tasks | DONE | All 10 control files landed as predicted on the SecuritySet task; the IndustrySet task's gold itself fails the kernel audit (7 of 12 theorems depend on `Lean.ofReduceBool`, i.e. `native_decide`) |
| 3. Lean check, 5 rule-built conditions x 256 tasks | IN PROGRESS | Gold: 256/256 compile; 159/256 pass the kernel audit; 97 depend on `native_decide` (IndustrySet 75/79, SecuritySet 18, HumanEval 2, CSSet 1, EasySet 1); 0 use `sorry`; 156 pass every check. Other 4 conditions running |
| 4. Draw sample (rule) and targeted shadowing set | DONE | 30 tasks (SecuritySet 18, IndustrySet 4, 2 each from the other splits; deviation D1 in README), 8 targeted-shadowing tasks, 4-task exploratory IndustrySet extension |
| 5. LLM-built and prompt conditions on the sample | IN PROGRESS | 30 x 7 + 4 x 7 + 8 x 1 Opus 5.5 generations |
| 6. Lean check and blind judge on the sample | PENDING | |
| 7. Analysis, comparison with TinyVeriBench-256 | PENDING | |
| 8. Light QA (Codex GPT-6 Astra), fixes | PENDING | |

**TLDR-end:** [trustworthy-theorem-judges: experiment 23 VB256 gaming] Running; no VB256 result has been read yet.
