# Experiment 14: ② (pick by train correlation) versus ④ (pick by train cross-entropy) on a large open-weight judge pool

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/14_open_weight_judge_pool_corr_vs_ce_80_20/README.md>

**TLDR:** Experiment 12 asked ② vs ④ on five cached judges. Here 15 open-weight models x the three experiment-100 prompts (H0, H1, H2) scored the same 75 expert-rated artifacts on free mercury2 GPUs (vLLM, no paid API), giving 39 usable open judges; ② vs ④ was rerun on the open pool, on old five plus open (44 judges), and on the old five again. Result is mixed, not a clean CE win: on RPS ④ beats ② as mixtures on the open and combined pools, ties on the old five, and ② beats ④ with the best single judge on the combined pool. The open judges are weak (median Pearson with the human mean 0.06). Details: [results.md](results.md).

This went straight to `main` as the next numbered experiment folder (no branch).

## Files

- [results.md](results.md): tables (RPS first, then CE, TVD, Spearman, Pearson; ②−④ with 95% task-bootstrap intervals), per-judge table, harness, models, nodes, limits.
- [results/](results/): `old5/`, `open/`, `all/` (results.json, per_artifact.json, run.log), `judge_table.json`, `judge_scores.json` (judge scores only), `judge_parse_stats.json`, `raw_judge_outputs/` (model outputs and slot logs).
- [scripts/](scripts/): `render.py` (prompts), `run_slot.py` (vLLM driver), `assemble.py` (parse, drop and fill rules), `nnls_pearson.py` and `check_nnls.py` (Pearson mixture solver for pools above 8 judges), `run_pool.py` (experiment 12's runner with that solver), `judge_table.py`, `make_report14.py`.
- [agent_log.md](agent_log.md): what was run, where, and the issues.

## Rebuild

Human ratings are private and not committed. To rebuild: build the human rows with experiment 12's `build_dataset.py` (veribench checkout, commit `be287d9`), run `scripts/assemble.py` on `results/raw_judge_outputs/` to get the dataset, then `scripts/run_pool.py --data <dataset> --out <dir>` (1,000 splits, 10,000 bootstrap draws), then `scripts/make_report14.py`. To regenerate judge outputs: `scripts/render.py`, then `scripts/run_slot.py` on a GPU host with vLLM 0.11.0.

## Limits

Weak judges, 25 tasks, 5 test tasks per split, prompts of the old pool were developed on the original train split, one run of each sampled judge, no Lean check and no DT, no ③. See the end of [results.md](results.md).
