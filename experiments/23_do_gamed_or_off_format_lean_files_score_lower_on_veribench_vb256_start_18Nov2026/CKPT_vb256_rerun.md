# Checkpoint: experiment 23 VB256 rerun

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/23_do_gamed_or_off_format_lean_files_score_lower_on_veribench_vb256_start_18Nov2026/CKPT_vb256_rerun.md>

## State (edit in place; at most 30 lines)

- Owner: Claude Code session started by the coordinator `local_4db118d6-5f99-4198-91d3-cccdf7e7ba65` (Opus 5.5, max effort), on Brando's Mac, repo `~/trustworthy-theorem-judges`, branch `main`.
- Authorization: Brando, chat 11-19-2026, "Yes, rerun on VB256" (relayed by the coordinator). No paid API; no VeriBench prover; light QA (one Codex round).
- Notifier (Rule 14/70): this session sends `[RUN START]` and `[RUN DONE]` to brando.science; the coordinator does not.
- Design: README.md (pre-registered 11-19-2026). Live results: results.md.
- Phase: 1 (import) done; next the smoke test, then the Lean check on 256 tasks.
- Resume commands (from `scripts/`):
  1. `python3 build_variants.py vb256`
  2. `python3 gate.py vb256 5 --kernel-audit`
  3. `python3 draw_vb256_sample.py`
  4. `python3 generate_llm_variants.py vb256_sample30 10` and `python3 generate_llm_variants.py vb256_perm_sorted_pairwise 4`
  5. `python3 gate.py vb256_sample30 5 --kernel-audit --conditions=<LLM and prompt conditions>` and the same for `vb256_perm_sorted_pairwise`
  6. `python3 judge.py vb256_sample30 6` and `python3 judge.py vb256_perm_sorted_pairwise 6 --conditions=faithful_gold_copy,shadowed_perm_sorted_pairwise`
  7. `python3 analyze_vb256.py`
- All steps are idempotent: generation and judge replies are cached by file; delete a cached file only to redo a recorded infrastructure failure.

## Log (append one dated line per event)

- 11-19-2026 15:05 PST: folder renamed, TinyVeriBench-256 run moved to `expt_v1_tinyveribench256/` (summaries reproduce byte-identically), VB256 imported (256/256), design pre-registered.
