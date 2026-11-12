# Experiment 16 results: ③ versus ④ versus ②, 1,000 task-grouped 20/5 splits

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/16_formulation3_val_selection_vs_4/results.md>

**TLDR:** Choosing the judge by validation loss (③) did not beat fitting by loss on all 20 train tasks (④) on held-out tasks. ③ by validation RPS is worse on RPS than ④ (+0.021, interval above 0) and ③ by validation CE collapses to the constant forecast (picked in 996 of 1,000 splits). ② and ④ still tie on RPS. Retrospective, cached judges, 25 tasks, no model calls, $0.

Harness: no LLM in the loop; cached scalar ratings of five judges (VeriBench experiment 100, Vals Valkyrie harness, models gpt-6-sol-high and claude-opus-5-5) re-used, fitted and ranked by a CPU script (Claude Code, Sonnet 5.5 wrote and ran it). 1000 splits, 75 artifacts, 25 tasks, 10,000-draw task bootstrap.

## Held-out test metrics (mean over artifacts, then splits)

| Method | RPS (main, lower better) | CE | TVD |
|---|---|---|---|
| constant (train marginal) | 0.1836 | 1.852 | 0.6818 |
| equal-weight mixture | 0.1496 | 5.431 | 0.5311 |
| ② mixture maximizing train Pearson (20 train tasks) | 0.1419 | 5.787 | 0.5222 |
| ④ mixture minimizing train CE (20 train tasks, no validation) | 0.1362 | 5.413 | 0.5098 |
| ③ pick by validation RPS (15 fit / 5 val), refit on all 20 | 0.1573 | 5.420 | 0.5622 |
| ③ pick by validation RPS, keep the 15-task fit | 0.1562 | 5.412 | 0.5607 |
| ③ pick by validation CE, refit on all 20 | 0.1834 | 1.867 | 0.6812 |
| ③ pick by validation CE, keep the 15-task fit | 0.1850 | 1.892 | 0.6813 |

## Paired differences, task bootstrap 95% interval (first minus second; negative = first better for RPS, CE, TVD)

| Comparison | RPS | CE | TVD |
|---|---|---|---|
| ③ pick by validation RPS (15 fit / 5 val), refit on all 20 minus ④ mixture minimizing train CE (20 train tasks, no validation) | +0.0210 [+0.0144, +0.0280] | +0.007 [-0.309, +0.328] (includes 0) | +0.0524 [+0.0362, +0.0691] |
| ③ pick by validation RPS, keep the 15-task fit minus ④ mixture minimizing train CE (20 train tasks, no validation) | +0.0200 [+0.0136, +0.0267] | -0.001 [-0.316, +0.318] (includes 0) | +0.0509 [+0.0357, +0.0668] |
| ③ pick by validation CE, refit on all 20 minus ④ mixture minimizing train CE (20 train tasks, no validation) | +0.0471 [+0.0008, +0.0942] | -3.546 [-4.883, -2.275] | +0.1714 [+0.0769, +0.2703] |
| ③ pick by validation RPS (15 fit / 5 val), refit on all 20 minus ② mixture maximizing train Pearson (20 train tasks) | +0.0154 [+0.0020, +0.0284] | -0.367 [-0.578, -0.149] | +0.0400 [+0.0154, +0.0654] |
| ④ mixture minimizing train CE (20 train tasks, no validation) minus ② mixture maximizing train Pearson (20 train tasks) | -0.0056 [-0.0181, +0.0059] (includes 0) | -0.374 [-0.693, -0.101] | -0.0124 [-0.0363, +0.0123] (includes 0) |
| ④ mixture minimizing train CE (20 train tasks, no validation) minus equal-weight mixture | -0.0133 [-0.0240, -0.0027] | -0.018 [-0.080, +0.051] (includes 0) | -0.0213 [-0.0428, +0.0025] (includes 0) |
| ④ mixture minimizing train CE (20 train tasks, no validation) minus constant (train marginal) | -0.0473 [-0.0947, -0.0008] | +3.561 [+2.286, +4.903] | -0.1720 [-0.2713, -0.0772] |

## Secondary columns: correlation of judge mean with human mean on the test tasks (task-attributed split values; positive = first higher)

| Comparison | Pearson | Spearman |
|---|---|---|
| ③ pick by validation RPS (15 fit / 5 val), refit on all 20 minus ④ mixture minimizing train CE (20 train tasks, no validation) | -0.022 [-0.026, -0.018] | +0.001 [-0.005, +0.007] (includes 0) |
| ③ pick by validation CE, refit on all 20 minus ④ mixture minimizing train CE (20 train tasks, no validation) | -0.049 [-0.094, -0.007] | +0.035 [-0.028, +0.096] (includes 0) |
| ③ pick by validation RPS (15 fit / 5 val), refit on all 20 minus ② mixture maximizing train Pearson (20 train tasks) | -0.035 [-0.047, -0.022] | -0.061 [-0.072, -0.050] |
| ④ mixture minimizing train CE (20 train tasks, no validation) minus ② mixture maximizing train Pearson (20 train tasks) | -0.013 [-0.023, -0.000] | -0.063 [-0.073, -0.052] |

Mean test-set correlation over splits (undefined when the forecast is constant): constant (train marginal): undefined; equal-weight mixture: Pearson 0.703; ② mixture maximizing train Pearson (20 train tasks): Pearson 0.730; ④ mixture minimizing train CE (20 train tasks, no validation): Pearson 0.717; ③ pick by validation RPS (15 fit / 5 val), refit on all 20: Pearson 0.694; ③ pick by validation RPS, keep the 15-task fit: Pearson 0.694; ③ pick by validation CE, refit on all 20: Pearson 0.662; ③ pick by validation CE, keep the 15-task fit: Pearson 0.660.

## What ③ picked

Winner counts over the 1,000 validation rankings: by validation RPS pearson_mixture 304, ce_shrink_0.0 300, constant 153, single_H0_sol 87, ce_shrink_0.5 38, ce_shrink_0.25 38, ce_shrink_1.0 29, single_H2_opus 23, ce_shrink_0.75 15, single_H2_sol 9, single_H0_opus 4. By validation CE constant 996, ce_shrink_0.5 2, ce_shrink_0.25 1, ce_shrink_1.0 1.

## Plain reading

- Validation selection does not help here. With 15 fit and 5 validation tasks the ranking of candidates is noisy, and the candidates differ little, so the pick probably often lands on a worse one (single judge or constant) than the plain 20-task CE fit (an explanation I did not test).
- Validation CE is dominated by the judges' near-zero probabilities on some ratings (CE of any mixture is about 5.4 against 1.85 for the constant), so ③ by CE returns the constant almost always, which has the worst RPS and undefined correlations.
- ② (Pearson mixture) and ④ (CE mixture) remain a tie on RPS (-0.006 [-0.018, +0.006]); ④ wins CE and ② wins the correlation columns, as in experiment 12.

## What was not checked

- Five test tasks and five validation tasks per split is tiny; the 1,000 splits reuse the same 25 tasks, so the intervals come from the task bootstrap only and the true uncertainty is wider than the number of splits suggests.
- The candidate family is small (five cached judges, mixtures). No new prompts, no agent search and no model calls, so this does not test ③ as a prompt or model search. The cached judges' prompts were developed with the original train split of these ratings, so held-out tasks may have been seen at design time.
- Validation RPS as the ③ loss follows the current priority plan; the literal CE version is shown as the second ③ row. Folds are grouped by task, not by task family or rater.
- The primary reading ("refit on all 20") and the secondary reading ("keep the 15-task fit") were both declared in PROTOCOL.md before the full run and both are shown.
