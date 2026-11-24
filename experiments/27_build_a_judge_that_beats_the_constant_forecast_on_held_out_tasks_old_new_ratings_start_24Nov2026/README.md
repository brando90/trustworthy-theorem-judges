# Experiment 27: build a judge that beats the constant forecast on held-out tasks (old + new human ratings), start 11-24-2026

**Dated:** 11-24-2026. **TLDR:** train/validation/test splits by task over the 25 old and 25 new rated tasks, dated anonymised copies of the ratings, a CE-fitted judge search on train and validation, one evaluation on test (RPS, CE, TVD first, with 95% task-bootstrap intervals). Status: pre-registered 11-24-2026; results go in RESULTS.md.

- [PREREG.md](PREREG.md): the plan, committed before any run.
- [data_11-24-2026/](data_11-24-2026/): dated copies of the human ratings (old, new), the cached H2 judge scores and the task splits.
- [scripts/](scripts/): code (CPU unless it says model calls).

## Result (Tue 11-24-2026)
Verdict under the pre-registration: **promising**, not works. See [RESULTS_11-24-2026.md](RESULTS_11-24-2026.md) (pooled test RPS 0.075 vs 0.110 for the set-aware constant, paired -0.035 [-0.076, +0.002]; CE 0.97 vs 1.19; TVD 0.35 vs 0.48).
