# Existing data for the objective comparison

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/06_information_loss_vs_correlation_judge_selection/DATA_INVENTORY.md>

**TLDR:** Five complete cached scalar judges and individual historical human ratings allow a zero-new-inference exploratory comparison. They do not provide native six-category probability forecasts or a fresh test set.

Read-only inventory verified on 11-06-2026 by the historical-import worker. Local source repository: `/Users/brandomiranda/veribench`; use committed blobs, not potentially changed working-tree files. No sealed new human ratings were opened. Keep all per-item data and participant identifiers private.

## Primary source

Commit: `be287d9bb2f7bd35ba6db1b8735c9ba10d00eade`.
Root: `experiments/100_karpathy_recipe_tc_judge_search_human_train_val_test/`.
Human observations: `inputs/items.jsonl`, 75 artifacts / 25 tasks. Individual integer ratings 0–5 are available, not merely means.

- Three expert columns: 195 observed ratings; two experts cover all 75 artifacts, the third covers 45.
- All five rater columns: 345 observed ratings; keep this expanded panel secondary to the expert target.
- Historical training: 30 artifacts / 10 tasks / 78 expert ratings.
- Historical validation: 15 artifacts / 5 tasks / 39 expert ratings.
- Historical test: 30 artifacts / 10 tasks / 78 expert ratings.
- Join using `item`, group using `task`, original split using `split`. Preserve reference/candidate hashes and flags `ref_placeholder_at_annotation` and `ref_ambiguous_in_window`.

## Five complete scalar candidate caches

Paths below are relative to the primary root's `runs/`; read each `receipts/*.json`, filter `kind == "main"`, and retain the status ledger.

| Candidate | Training run | Validation/test run(s) |
| --- | --- | --- |
| H0 Sol | `w1_H0_sol_high` | `ab_H0_sol` |
| H0 Opus | `w1_H0_opus55_max` | `ab_H0_opus` |
| H1 Sol | `p3_i1_H1_sol_high` | `ab_H1_sol` |
| H2 Sol | `p3_i2_H2_sol_high` | `p4_val_H2_sol_high`, `p5_test_H2_sol_high` |
| H2 Opus | `p3_i3_H2_opus55_max` | `p4_val_H2_opus55_max`, `p5_test_H2_opus55_max` |

Each has 75 artifacts × 3 complete repeated scalar outputs; 1,125 historical calls total. The `ab_*` runs cover 45 artifacts; assign validation versus test from the human input manifest. Repeat indices are 1, 2, 3. Fields include `item`, `task`, `repeat`, `status`, `score_raw`, normalized `score`, `verdict`, hashes and configuration. Resolve exact model IDs from configuration/receipts before reporting model names; these table labels are historical run identifiers.

`score_raw` takes values 0–5. The verdict requests an integer `final_score_0_5`, qualitative confidence and rationale/checklist; it contains no native probability mass function or token probabilities. Never interpret Low/Med/High confidence as numeric probabilities. A histogram of three calls is a new, noisy empirical distribution estimator, which must be named as such. Pooling the two H2 members' six calls is also a new estimator, not the saved median-based ensemble's native probabilities.

Cheapest first phase: freeze these five repeated-rating histogram estimators, apply the identical predeclared probability floor, select among them under each objective using validation tasks, and evaluate held-out tasks. Add training-fitted distribution heads only as a separately named condition. Repeated sampling of model scores and repeated human ratings represent different sources of variation.

## Optional out-of-fold historical receipts

Root: `research_archive/experiments/104_fsc_judge_5fold_cross_validation_all_75_expert_labels/`.
Raw receipts are present at commit `f1bfbe3564f96444da42833b8f5a1f08c42c08d1` under `runs/{r1_sol_high,r1_opus55_max,r2_sol_high,r2_opus55_max}/receipts/`.

Repetition 1 has 75 × 5 complete calls per model. Repetition 2 has 375 complete Sol calls and 374 complete Opus calls plus one `NONCLEAN_FINISH`; one Opus item has four usable repeats. These use fold-specific judges; do not treat them as one fixed judge across folds. `results/per_item_oof.csv` rounds human means, so use the primary source's individual ratings instead. Audit whether a new outer split conflicts with the old fold-specific training exposure before reuse.

## Claim limits

All these human ratings and the old test split have prior exposure. New nested splitting does not undo it or the upstream prompt-selection history. The cached candidates come from one older solver-output population; they cannot establish transfer across unseen solver or rater families. The analysis is retrospective feasibility, with fresh human confirmation still required.
