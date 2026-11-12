# Results: audit of the GPT-5.3-Codex rubric judge on 75 rated outputs

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/archive/19_audit_gpt_5_3_codex_rubric_judge_on_75_rated_outputs_start_12Nov2026_end_12Nov2026/results.md>

**TLDR:** **Verdict: COMPLETE.** The launch page's r = 0.61 reproduces exactly, but alone it supports only a moderate, uncertain association: r = 0.614 [0.213, 0.821], Spearman 0.375 [0.013, 0.668], a judge 0.825 [0.594, 1.082] points below the pooled raters, and agreement that rises to Spearman 0.565 [0.197, 0.800] only on the 51 outputs whose reference theorems the judge actually shared with the raters.

All values: 75 outputs from 25 tasks unless stated; 0–5 scale; brackets are 95% percentile intervals from 10,000 task-bootstrap draws (seed 20261112), p-val=n/a; mean bias is judge minus human (negative = stricter judge). Source: [the JSON](POSTHOC_CLI_RUBRIC_JUDGE_AGREEMENT_11-12-2026.json).

## Pooled target

| Statistic | Raw judge (mean of 3 calls) | Isotonic remapping, out of fold |
|---|---:|---:|
| Pearson r | 0.614 [0.213, 0.821] | 0.211 [−0.123, 0.505] |
| Spearman ρ | 0.375 [0.013, 0.668] | 0.046 [−0.320, 0.415] |
| Kendall τ_b | 0.300 [0.021, 0.545] | 0.042 [−0.232, 0.320] |
| r − ρ (paired) | 0.238 [0.061, 0.408] | 0.165 [−0.027, 0.342] |
| ICC(A,1) / ICC(C,1) | 0.429 [0.110, 0.662] / 0.613 [0.206, 0.819] | 0.167 / 0.165 |
| Judge mean / human mean | 2.382 / 3.207 | 3.190 / 3.207 |
| Mean bias | −0.825 [−1.082, −0.594] | −0.018 [−0.332, 0.301] |
| Mean absolute error | 0.889 [0.695, 1.122] | 0.628 [0.432, 0.848] |
| Error minus out-of-fold constant (0.705) | +0.184 [−0.098, 0.440] | −0.077 [−0.178, 0.020] |

Receipt p-values (independent-output tests of zero association): raw 4.78e-9, 9.03e-4, 4.49e-4; remapped 0.069, 0.694, 0.637. The remapping keeps each fold's order (Spearman 0.596 and 0.238 within folds) but scores each fold with the other fold's map, shifting the fold with human mean 2.966 to predictions averaging 3.376 and the fold with mean 3.468 to 2.989.

## Granularity

| View | Pearson r | Spearman ρ |
|---|---:|---:|
| Task means (25) | 0.685 [0.150, 0.911] | 0.474 [−0.005, 0.825] |
| Centered within task (75) | 0.358 [0.055, 0.635] | 0.327 [0.021, 0.601] |
| Spearman inside each task, averaged over 20 tasks with varying scores | | 0.255 [−0.073, 0.579] |

## Rater targets (receipt point estimates, each rebuilt from the rating files to 1e-12)

| Target | Outputs | Human mean | r | ρ | Judge − human |
|---|---:|---:|---:|---:|---:|
| Lenient group (participant 1 earlier passes ×2, participants 4, 5) | 75 | 3.573 | 0.702 | 0.603 | −1.191 |
| Five raters, final prompt | 75 | 2.989 | 0.500 | 0.339 | −0.607 |
| Expert group (participant 1 final, participants 2, 3) | 75 | 2.631 | 0.372 | 0.300 | −0.249 |
| Single raters | 44–75 | 2.227–3.867 | 0.275–0.742 | 0.209–0.442 | −1.484 to +0.303 |

## Did the judge read the raters' files?

All 75 candidate files are byte-identical to the rated ones. The judge-run reference states the rated theorems for 51 outputs (14 tasks with identical bytes, 3 with a later file with the same statements). For the other 24 outputs (8 tasks: all five placeholder-reference security tasks, two other changed references, one third version stating 7 theorems where the rated one stated 5), the statements differ; 21 of the 24 differ even in theorem count.

| Outputs (tasks) | Pearson r | Spearman ρ | ICC(A,1) | Mean bias |
|---|---:|---:|---:|---:|
| Matched statements, 51 (17) | 0.775 [0.371, 0.915] | 0.565 [0.197, 0.800] | 0.617 [0.216, 0.794] | −0.587 [−0.760, −0.393] |
| … and reference unchanged during rating, 36 (12) | 0.764 [0.357, 0.914] | 0.632 [0.237, 0.863] | 0.624 [0.216, 0.807] | −0.623 [−0.851, −0.345] |
| Different statements, 24 (8) | 0.522 [−0.011, 0.784] | 0.479 [−0.121, 0.836] | 0.265 [−0.002, 0.572] | −1.330 [−1.838, −0.866] |

These subsets are post hoc, and the matched subset contains no security tasks, so reference mismatch and task family are confounded.
