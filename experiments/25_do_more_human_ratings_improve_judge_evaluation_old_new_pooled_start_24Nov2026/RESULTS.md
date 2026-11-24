# Results: does pooling old and new human ratings give a better evaluation of the trustworthy judge?

**Dated:** 11-24-2026 (run Tue 11-24-2026, ratings frozen at about 10:38 PST; see [results/INVENTORY.md](results/INVENTORY.md)). Pre-registration: [PREREG.md](PREREG.md), commit 3f5a460 (before any judge call on the new artifacts). Run by ub9sc (ultimate brando9 scalable coworker) for Brando Miranda.

**TLDR:** Yes for the evaluation, not for the judge. Pooling old (25 tasks, 75 artifacts, 195 ratings) and new (25 tasks, 100 artifacts, 247 ratings) halves the width of the RPS interval relative to old alone (0.60x for GPT-6 Astra, 0.64x for Claude Opus 5.5), the Spearman interval inside each set shrinks about as sqrt(2) predicts, and the spread of the estimate drops from k = 10 to k = 25 tasks. But (1) the pooled "judge beats constant" result is an artifact of mixing two rating levels: against a constant computed inside each set, Astra is tied (+0.002) and Opus is not clearly better (-0.018, interval -0.048 to +0.013); (2) both judges overscore the old set by about half a point and more data does not change that; (3) only 247 of 3,300 sheet rows are back, 73% of them are 5s. Cost: $0 extra (plans only); list-price equivalent about $10 to $15.

## What was run (harness and model for every result)
| Judge | Old artifacts (75) | New artifacts (100, 3 repeats each) |
|---|---|---|
| GPT-6 Astra, reasoning high, H2 prompt | cached exp 21/22 run, OpenAI Responses API | Codex CLI one-turn, read-only sandbox, no tools, on the Codex plan |
| Claude Opus 5.5, H2 prompt | cached exp 21/22 run, Vals gateway, effort max | Claude Code one-turn, no tools, effort high, Stanford Claude plan |

Pooled rows therefore mix harnesses (and, for Opus, effort). That is a limitation, not corrected. The frozen H2 prompt and the same four leave-task-out demos were used on the new artifacts; frozen request file sha256 6f5999833a09cd434005ff5d0d672a3c602fdf4c29b1df58173840883cd5ad7e (300 requests, all 600 calls returned a parsable score). The 5 other cached judges exist on the old set only and are in results/aggregates.json.

## Q1. Interval widths: old alone, new alone, pooled (task bootstrap, 10,000 draws, seed 20261124)
| Judge | Set | Artifacts / tasks / ratings | RPS (95% CI) | Constant RPS | CE | TVD | Spearman | Pearson |
|---|---|---|---|---|---|---|---|---|
| GPT-6 Astra | old | 75 / 25 / 195 | 0.207 [0.150, 0.269] | 0.183 | 8.50 [6.92, 9.95] | 0.629 [0.522, 0.727] | 0.65 [0.35, 0.88] | 0.65 [0.29, 0.87] |
| GPT-6 Astra | new | 100 / 25 / 247 | 0.055 [0.032, 0.080] | 0.070 | 3.42 [2.08, 4.84] | 0.253 [0.157, 0.355] | 0.59 [0.32, 0.78] | 0.81 [0.65, 0.90] |
| GPT-6 Astra | pooled | 175 / 50 / 442 | 0.120 [0.087, 0.158] | 0.164 | 5.60 [4.40, 6.80] | 0.414 [0.329, 0.500] | 0.79 [0.66, 0.88] | 0.78 [0.60, 0.89] |
| Claude Opus 5.5 | old | 75 / 25 / 195 | 0.179 [0.135, 0.223] | 0.183 | 8.10 [6.63, 9.49] | 0.600 [0.498, 0.696] | 0.77 [0.55, 0.90] | 0.78 [0.61, 0.89] |
| Claude Opus 5.5 | new | 100 / 25 / 247 | 0.041 [0.027, 0.056] | 0.070 | 2.42 [1.56, 3.29] | 0.193 [0.128, 0.258] | 0.65 [0.41, 0.80] | 0.90 [0.74, 0.95] |
| Claude Opus 5.5 | pooled | 175 / 50 / 442 | 0.101 [0.074, 0.131] | 0.164 | 4.85 [3.81, 5.98] | 0.368 [0.292, 0.448] | 0.86 [0.77, 0.91] | 0.86 [0.77, 0.92] |

Constant = pooled human marginal, leave-one-task-out; on the pooled row it is computed over both sets together. Lower is better for RPS, CE, TVD.

Interval width, pooled divided by old (Astra / Opus): RPS 0.60 / 0.64, CE 0.80 / 0.76, TVD 0.84 / 0.79, Spearman 0.41 / 0.39, Pearson 0.51 / 0.54. Two cautions. (a) RPS widths scale with the level, and the new set has a much lower RPS level; relative to the estimate the RPS interval does not shrink (0.57 old, 0.60 pooled for Astra; 0.49 old, 0.56 pooled for Opus). (b) The pooled Spearman and Pearson are higher partly because the two sets differ in rating level (see next section); with ranks taken inside each set, Spearman is 0.62 [0.42, 0.77] for Astra and 0.71 [0.56, 0.81] for Opus, whose widths are 0.66 and 0.72 of the old-alone widths, close to the sqrt(2) prediction (0.71).

## Pooled results need set-aware baselines ([results/setaware.json](results/setaware.json))
| Judge | Judge RPS pooled | Set-aware constant RPS | Difference (95% CI) | Spearman, ranks inside each set | Mean judge minus human, old set (score points) | Same, new set |
|---|---|---|---|---|---|---|
| GPT-6 Astra | 0.120 | 0.118 | +0.002 [-0.030, +0.036] | 0.62 [0.42, 0.77] | +0.51 [+0.04, +0.90] | +0.06 [-0.08, +0.20] |
| Claude Opus 5.5 | 0.101 | 0.118 | -0.018 [-0.048, +0.013] | 0.71 [0.56, 0.81] | +0.56 [+0.26, +0.87] | +0.13 [+0.04, +0.21] |

The pooled constant (0.164) is a poor baseline because the new set is mostly 5s and the old set is not; against it both judges look clearly better (-0.044 and -0.064), but that gap comes from mixing the sets, not from the judge.

## Q2. Human ceiling (split-half, 1,000 random splits per artifact set; Spearman-Brown corrected)
| Set | Artifacts with >= 2 raters | Mean raters | Split-half RPS | Split-half Pearson | Spearman-Brown reliability | Correlation ceiling (sqrt) | Irreducible RPS floor |
|---|---|---|---|---|---|---|---|
| old | 75 | 2.60 | 0.128 | 0.825 | 0.904 | 0.951 | 0.045 |
| new | 100 | 2.47 | 0.062 | 0.778 | 0.875 | 0.936 | 0.019 |
| pooled | 175 | 2.53 | 0.090 | 0.887 | 0.940 | 0.969 | 0.030 |

The split-half Spearman is 0.83 (old) and 0.48 (new): the new set has many ties (73% of ratings are 5s), so rank correlation is a weak instrument there; Pearson is the fairer ceiling on it. The pooled reliability is inflated by the between-set level difference. The best judge on old (Opus, Pearson 0.78) sits well below the ceiling (0.95); on new Opus Pearson 0.90 is close to its ceiling (0.94).

## Q3. Learning curve (GPT-6 Astra; 40 random subsets per k, 200 bootstrap draws each; [figure](results/learning_curve.png))
| k tasks | old: RPS width / SD of estimate | new: RPS width / SD | pooled: RPS width / SD | pooled: Spearman width / SD |
|---|---|---|---|---|
| 5 | 0.205 / 0.058 | 0.088 / 0.025 | 0.187 / 0.057 | 0.64 / 0.28 |
| 10 | 0.177 / 0.038 | 0.067 / 0.015 | 0.154 / 0.035 | 0.54 / 0.11 |
| 15 | 0.141 / 0.023 | 0.059 / 0.011 | 0.119 / 0.027 | 0.37 / 0.09 |
| 20 | 0.133 / 0.012 | 0.051 / 0.006 | 0.099 / 0.023 | 0.29 / 0.07 |
| 25 | 0.115 / 0.000 | 0.047 / 0.000 | 0.094 / 0.015 | 0.27 / 0.05 |
| 30 | | | 0.087 / 0.017 | 0.27 / 0.05 |
| 40 | | | 0.077 / 0.008 | 0.22 / 0.03 |
| 50 | | | 0.070 / 0.000 | 0.21 / 0.00 |

The SD is 0 at the full set by construction (one subset). The width keeps falling past 25 tasks, but slowly after about 30: the Spearman interval goes from 0.54 at 10 tasks to 0.27 at 25 and 0.21 at 50 (still +/-0.1). Spearman intervals with 10 tasks (the old train split) are wide whatever the data: 0.8 on old alone.

## Q4. What more data does not fix
- Calibration: both judges overscore the old set by about half a point on average (Astra +0.51, Opus +0.56; intervals above 0). Pooling does not shrink that bias; it only measures it more tightly.
- Against a constant computed inside each set, neither judge is clearly better on the pooled data (table above), and on old alone neither beats the constant (Astra +0.025, Opus -0.003; both intervals contain 0).
- On the new set both judges beat the within-set constant (Astra -0.015 [-0.034, +0.002], Opus -0.029 [-0.050, -0.009]), but that constant is nearly "all 5s", an easy bar.

## Pre-registered predictions and decision rule
1. Pooled widths about sqrt(2) narrower than old alone: RPS 0.60x and 0.64x (more than predicted, partly the level effect); Spearman inside sets 0.66x and 0.72x (as predicted). Spearman with k <= 10 stays wide: confirmed.
2. New ceiling lower or comparable to old: Spearman-Brown 0.875 vs 0.904 (comparable); split-half RPS is lower on new (0.062 vs 0.128) because 5s dominate. Confirmed in the correlation sense.
3. Judge RPS not clearly better than the constant on either set: true on old; false on new for Opus (clearly better, -0.029), borderline for Astra. Partly wrong.
4. Spearman and RPS rank judges differently on at least one pair: confirmed on old (H0_sol has the lowest Spearman, 0.55, but the 3rd-best RPS of the 8 single judges, 0.186, ahead of H2_sol61, H1_sol, H2_sol, H2_astra and H0_opus).
- **Decision rule (a)** pooled RPS interval width <= 0.8 of old alone: met (0.60 and 0.64). **(b)** spread of the estimate at k = 25 below that at k = 10: met (0.015 vs 0.035 pooled). **(c)** ordering of judges by RPS stable: read as the task-bootstrap share of draws in which Opus has lower RPS than Astra: 96% on old and 95% on new (two judges only on new). All three met: "better evaluation" = yes, with the set-aware caveat above. It says nothing about the judge being better.

## Deviations from the pre-registration
- Opus on new artifacts: effort high on the Stanford Claude plan, not effort max via the Vals gateway (the gateway would have been paid per call; the personal Claude login had expired). Astra on new artifacts: Codex CLI on the plan, not the API.
- Learning curve: 40 subsets x 200 bootstrap draws per k (the pre-registration said 300 x 1,000) because of compute time on a shared 4-CPU machine.
- Decision rule (c) was computed as a bootstrap share, not over k-task subsets.
- Added (not pre-registered): the set-aware constant, within-set ranks and the judge-minus-human bias, in [scripts/setaware.py](scripts/setaware.py).
- GPT-6 Astra on the new artifacts ran on the personal Codex plan (about 10M input tokens); that plan reached its usage limit afterwards (resets Nov 29), so the QA below ran on Claude.

## Light QA ([results/QA.md](results/QA.md))
An independent recomputation by Claude Opus 5.5 (Stanford Claude plan, own code, only anonymised per-artifact numbers as input) reproduced every headline number above (RPS, CE, TVD, Spearman, Pearson, constant RPS, split-half RPS) to 4 decimals and the new-set RPS intervals to within 0.001. It is not a second model family: the OpenAI lanes (personal Codex at its limit, Stanford Codex sandbox failing to start, Vals Codex sign-in blocked) were unavailable.

## Limits
- Only 247 of 3,300 sheet rows are back, from 5 raters (100, 100, 30, 16, 1 ratings); 55 artifacts have exactly 2 ratings, so per-artifact human distributions are noisy. Later waves (Wed 11-25 6 PM PT, Thu 12-03) need a re-run.
- 73% of new ratings are 5s: a ceiling effect that makes new-set RPS look small and rank correlations unstable.
- Old and new tasks differ, harnesses differ between old and new judge calls, and only two judges have scores on the new set.
- No Lean proof check and no differential testing.

**TLDR-end:** [trustworthy judge: experiment 25] Pooling old and new ratings narrows the RPS interval to 0.60x to 0.64x of old alone and steadies the estimate (50 tasks, RPS +/-0.035), but against a set-aware constant neither judge is clearly better and both overscore old items by about half a point; re-run when the 11-25 and 12-03 rating waves arrive.
