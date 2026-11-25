# Interim re-run of experiment 25 with every rating sheet returned so far (dated 11-24-2026, ratings read about 19:12 PST)

**Label: INTERIM.** Not final. The Wed 11-25-2026 6 PM PT and Thu 12-03-2026 rating waves are not in. Compares against the 11-24-2026 10:38 PST run in [RESULTS.md](RESULTS.md). Run by ub9sc (ultimate brando9 scalable coworker) for Brando Miranda. Cost: $0 extra (plans only; no new judge calls).

**TLDR: no, the results are not starting to get better.** Only 3 ratings were added and 7 were edited since the morning (250 ratings, 100 new artifacts, 25 new tasks; pooled 445 ratings, 175 artifacts, 50 tasks). Every number moved by less than its interval: against a constant computed inside each set, Astra is tied (RPS difference +0.000, 95% interval -0.031 to +0.034) and Opus is not clearly better (-0.017, -0.047 to +0.014); both judges still overscore the old files by about half a point (+0.51, +0.56). The only visible shift is on the new set, from the 7 edited ratings of one rater (mostly 4 to 5): Astra RPS 0.055 -> 0.052, CE 3.42 -> 3.14. Intervals did not shrink (3 added ratings on 100 artifacts). Real change needs the 11-25 and 12-03 waves.

## Harness and model for every result
Judge scores are unchanged from RESULTS.md (no new artifacts exist, so nothing needed judging): GPT-6 Astra and Claude Opus 5.5, H2 prompt; old files from the cached exp 21/22 runs, the 100 new files from the exp 25 runs (Astra via Codex CLI, Opus 5.5 via Claude Code on the Stanford plan). Analysis: scripts/analyze.py and scripts/setaware.py, 10,000 task-bootstrap draws, same seed as RESULTS.md. Light QA: GPT-6 Astra via Codex CLI on the Vals plan (see below).

## Proper scores first (RPS, CE, TVD; lower is better), before (10:38) -> now (19:12), 95% task-bootstrap interval now
| Judge | Set | Ratings | RPS | CE | TVD | Constant RPS (set-aware / pooled) |
|---|---|---|---|---|---|---|
| GPT-6 Astra | old (75 files, 25 tasks) | 195 -> 195 | 0.207 [0.150, 0.269] (same) | 8.50 (same) | 0.629 (same) | 0.183 |
| GPT-6 Astra | new (100, 25) | 247 -> 250 | 0.055 -> 0.052 [0.031, 0.075] | 3.42 -> 3.14 [1.89, 4.45] | 0.253 -> 0.230 [0.138, 0.325] | 0.070 |
| GPT-6 Astra | pooled (175, 50) | 442 -> 445 | 0.120 -> 0.118 [0.085, 0.157] | 5.60 -> 5.44 [4.23, 6.67] | 0.414 -> 0.401 [0.315, 0.489] | 0.118 set-aware / 0.164 pooled |
| Claude Opus 5.5 | old | 195 | 0.179 [0.135, 0.223] (same) | 8.10 (same) | 0.600 (same) | 0.183 |
| Claude Opus 5.5 | new | 247 -> 250 | 0.041 -> 0.043 [0.029, 0.057] | 2.42 -> 2.42 [1.62, 3.24] | 0.193 -> 0.195 [0.132, 0.258] | 0.070 |
| Claude Opus 5.5 | pooled | 442 -> 445 | 0.101 -> 0.101 [0.075, 0.131] | 4.85 -> 4.85 [3.81, 5.99] | 0.368 -> 0.369 [0.294, 0.449] | 0.118 set-aware / 0.164 pooled |

Interval widths did not shrink: pooled RPS 0.072 (Astra) and 0.056 (Opus), the same as before; the old-alone width ratio is still 0.60 and 0.64.

## Does the judge beat a constant forecast? (set-aware, [setaware.json](results_interim_11-24-2026_1912/setaware.json))
| Judge | Pooled RPS | Set-aware constant | Difference, before -> now [95% interval now] | Spearman inside each set (secondary), before -> now | Mean judge minus human, old / new set |
|---|---|---|---|---|---|
| GPT-6 Astra | 0.118 | 0.118 | +0.002 -> +0.000 [-0.031, +0.034] | 0.62 -> 0.64 [0.44, 0.79] | +0.51 [+0.04, +0.90] / +0.05 [-0.08, +0.18] |
| Claude Opus 5.5 | 0.101 | 0.118 | -0.018 -> -0.017 [-0.047, +0.014] | 0.71 -> 0.69 [0.54, 0.80] | +0.56 [+0.26, +0.87] / +0.12 [+0.03, +0.21] |

Secondary correlations (Spearman, Pearson) now: Astra new 0.64 / 0.83, pooled 0.80 / 0.79; Opus new 0.61 / 0.89, pooled 0.85 / 0.86 (before: Astra new 0.59 / 0.82, Opus new 0.65 / 0.90). Pooled correlations are inflated by the difference in rating level between the two sets.

Opus has the lower RPS than Astra in 96% of bootstrap draws on old and 89% on new (95% before): the ordering of the two judges is unchanged.

## Human ceiling (new set, split-half)
Split-half Pearson 0.778 (same), Spearman-Brown reliability 0.875 (same), split-half RPS 0.058 (was 0.062). Still 74% of new ratings are 5s.

## Light QA by the other model family ([QA_INTERIM.md](results_interim_11-24-2026_1912/QA_INTERIM.md))
GPT-6 Astra (Codex CLI on the Vals plan) wrote its own recomputation script from the definitions only; the same numbers came out for all 30 point values (RPS, CE, TVD, Spearman, Pearson, constant RPS; 2 judges x old, new, pooled). Details and what was not checked are in the QA file.

## Limits
- 250 of 3,300 sheet rows are back; 74% of new ratings are 5s; new tasks differ from old ones; no Lean check.
- Pooled rows mix harnesses (old cached runs vs new runs).
- Not re-run in this interim: the learning curve, the exp 27 held-out judge test (frozen splits), the other 6 cached old judges.
- Next: re-run after the 11-25 6 PM PT wave and the 12-03 wave.

**TLDR-end:** [trustworthy judge: exp 25 interim] Not getting better yet: 3 ratings added and 7 edited since 10:38; against a set-aware constant Astra is tied (+0.000) and Opus not clearly better (-0.017); QA by GPT-6 Astra reproduced all 30 headline numbers.
