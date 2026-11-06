## Addendum 09-29-2026 (experiment 102 main session): rounding before ranking

The ensemble prediction is the mean of two member medians, and sums such as `(0.6 + 0.8) / 2` and `(0.4 + 1.0) / 2` differ in the last binary digit, so rank statistics computed on raw floats can split ties that should be one (experiment 102 `REPORT.md` finding 1). Recomputed from `results/per_item_oof.csv` with values rounded to 1e-6 before ranking (same metrics code, 10,000 task draws, seed 20260929):

| Quantity | As reported above | Ties preserved |
|---|---:|---:|
| Primary (repetition 1) Spearman [95% CI] | 0.602 [0.286, 0.834] | 0.603 [0.287, 0.836] |
| Primary Kendall τ-b / Pearson / ICC(A,1) | 0.496 / 0.621 / 0.593 | 0.498 / 0.621 / 0.593 |
| Repetition 2 Spearman | 0.654 | 0.660 |
| Experiment 100's frozen judge, all 75 items | 0.756 | 0.758 |
| On experiment 100's 45 held-out items: recipe vs frozen judge | 0.746 vs 0.834 | 0.749 vs 0.837, difference −0.089 [−0.270, 0.028] |
| Raters' instructions only, Opus / Sol (experiment 100 H0, k=3), all 75 items | — | 0.600 / 0.515 |

Every gate outcome is unchanged; the primary Spearman clears 0.60 by 0.003. The paper quotes the tie-preserving values.
