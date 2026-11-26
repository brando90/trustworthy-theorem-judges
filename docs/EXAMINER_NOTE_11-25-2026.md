# Examiner note (11-25-2026): new ratings and the 0.6/0.8/0.8 correlation issue

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/docs/EXAMINER_NOTE_11-25-2026.md>

**Date:** 11-26-2026. File name is the requested 11-25-2026 examiner note. Every number is copied from the named file. No rating sheet was re-synced.

**TLDR:** Train/validation/test Spearman $0.6400/0.8800/0.8257$ ("$0.6, 0.8, 0.8$") still does not mean the judge beats a constant forecast. With the old $195$ ratings plus the interim $250$ new-set ratings, a pooled correlation near $0.8$ is mostly the gap between the two sets, and neither frontier judge clearly beats a constant computed inside each set. On held-out tasks the experiment 27 judge is promising, not shown to work: ranked probability score (RPS) minus that constant is $-0.035$ $[-0.076, +0.002]$ $p$-val=n/a.

## The earlier issue

Selected judge in `experiments/archive/01_veribench_25_tasks_3_samples_5_raters_judge_evaluation_start_03May2026_end_29Sep2026`: `openai/gpt-6-sol-high` plus `anthropic/claude-opus-5-5-no-fallback`, H2 prompt, three calls per model. Re-score, no differential testing and no Lean check: `experiments/22_evaluate_veribench_judges_on_75_outputs_distribution_losses_vs_correlations_start_16Nov2026/EVAL_DOCUMENT_5_METRICS_11-16-2026.md`. Old set only, $25$ tasks, $75$ artifacts, $195$ ratings, splits $10/5/10$ tasks.

Spearman $0.6400$ (train, $30$ artifacts), $0.8800$ (validation, $15$), $0.8257$ (test, $30$). Pearson $0.6576$, $0.8601$, $0.8578$. Test Spearman interval $0.8257$ $[0.3162, 0.9656]$ $p$-val=n/a is the $10{,}000$-draw task-cluster bootstrap in `experiments/26_how_new_and_old_human_ratings_fix_06_08_08_and_expand_5metric_eval_start_24Nov2026/RESULTS_old_and_new_06_08_08_and_certjudge_11-24-2026.md`.

Test RPS (normalized; averaged inside each artifact, then equally over artifacts) was $0.1954$ $[0.1246, 0.2669]$ against $0.1836$ for the constant training-set rating histogram. Judge minus constant: $+0.0118$ $[-0.0898, +0.1085]$ $p$-val=$0.8244$ (two-sided paired task-cluster bootstrap). Leniency, mean judge minus mean human, was $+0.1811$ $[+0.0989, +0.2622]$ on $[0,1]$ (means $0.6533$ and $0.4722$), which that re-score calls nearly one point on the $0$–$5$ scale, and $55.0\%$ of test mean squared error. Correlation does not see that shift. Intervals resample these tasks only.

## What 250 new ratings plus the old 195 change

Interim, about 19:12 PST on 11-24-2026: `experiments/25_do_more_human_ratings_improve_judge_evaluation_old_new_pooled_start_24Nov2026/RESULTS_INTERIM_11-24-2026_1912.md`, `results_interim_11-24-2026_1912/INVENTORY_INTERIM.md`, `results_interim_11-24-2026_1912/setaware.json`. Different judges: GPT-6 Astra (reasoning high) and Claude Opus 5.5, H2 prompt. Old calls cached from experiments 21/22; new calls Codex CLI and Claude Code. No new judge calls. No differential testing.

Old $195$/$75$/$25$ unchanged. New $250$/$100$/$25$ ($3$ added and $7$ edited since the $247$-rating file). Pooled $445$/$175$/$50$. New ratings that are $5$: $185/250$ ($74.0\%$). Intervals: $10{,}000$ task-bootstrap draws, seed $20261124$ (`RESULTS.md` in that experiment). No $p$-value is stored.

Against a constant inside each set: Astra pooled RPS $0.118$ versus $0.118$, difference $+0.000$ $[-0.031, +0.034]$ $p$-val=n/a. Opus $0.101$ versus $0.118$, difference $-0.017$ $[-0.047, +0.014]$ $p$-val=n/a. Both intervals contain $0$. Pooled Spearman is $0.80$ and $0.85$; ranks inside each set are $0.64$ $[0.44, 0.79]$ and $0.69$ $[0.54, 0.80]$. On the $247$-rating sync (not recomputed at $250$), experiment 26 shows two within-cohort constants, which have no within-cohort correlation, still give pooled Pearson $0.6557$ $[0.5046, 0.7850]$ $p$-val=n/a, because artifact-equal human means are $0.5253$ (old) and $0.9143$ (new) on $[0,1]$.

Pooled RPS interval widths stay $0.072$ and $0.056$, and pooled/old width ratios stay $0.60$ and $0.64$, matching `RESULTS.md` there. Old-set leniency, in $0$–$5$ points: $+0.51$ $[+0.04, +0.90]$ and $+0.56$ $[+0.26, +0.87]$ $p$-val=n/a. New-set bias: $+0.05$ $[-0.08, +0.18]$ and $+0.12$ $[+0.03, +0.21]$. The extra ratings show where the pooled $0.8$ comes from. They do not show a gain on RPS.

## Experiment 27 held out: promising, not works

`experiments/27_build_a_judge_that_beats_the_constant_forecast_on_held_out_tasks_old_new_ratings_start_24Nov2026/RESULTS_11-24-2026.md` and `PREREG.md`. Freeze is the 12:58 PST export ($247$ new ratings), not the $250$ interim. Test scored once. Final judge: F8 (Astra H2 mean, Opus H2 mean, one-call H3 score, H3 expected score), ordinal cumulative logit fitted by cross-entropy, chosen on validation RPS, refit on train plus validation. H3: GPT-6 Astra, high, Codex CLI, one call per artifact. No differential testing.

Test: $20$ tasks, $70$ artifacts. Cross-entropy (CE) is the human histogram against the judge distribution floored at $10^{-6}$ and renormalised. Total variation distance (TVD) compares those distributions. Lower is better. Task bootstrap, $10{,}000$ draws, seed $20261124$. The registered rule is the interval, so $p$-val=n/a.

| Forecast | RPS | CE | TVD |
|---|---|---|---|
| Final judge | $0.075$ $[0.047, 0.109]$ | $0.97$ $[0.68, 1.30]$ | $0.35$ $[0.29, 0.44]$ |
| Constant inside each set | $0.110$ $[0.074, 0.151]$ | $1.19$ $[0.90, 1.50]$ | $0.48$ $[0.40, 0.56]$ |
| Earlier raw H2 | $0.100$ $[0.056, 0.154]$ | $4.12$ $[2.31, 6.22]$ | $0.33$ $[0.20, 0.48]$ |

Final minus set-aware constant: RPS $-0.035$ $[-0.076, +0.002]$, CE $-0.22$ $[-0.46, +0.01]$, TVD $-0.124$ $[-0.205, -0.055]$. Versus raw H2, RPS $-0.025$ $[-0.049, -0.005]$ is entirely below $0$; TVD $+0.024$ $[-0.059, +0.099]$ is not. "Works" (`PREREG.md` section 2) needs that RPS interval entirely below $0$ against both the set-aware constant and the earlier H2 judge, and CE and TVD point estimates below the constant. The constant comparison includes $0$ at $+0.002$, so the file's verdict is promising, not works. New test tasks alone ($10$ tasks): RPS $-0.027$ $[-0.057, -0.007]$, and CE and TVD intervals are also below $0$. Old test tasks: RPS $-0.045$ $[-0.129, +0.037]$. Pooled Spearman $0.89$ and Pearson $0.91$ are secondary; knowing only the set already reaches Spearman $0.75$.

## What still needs more human ratings

Only $250$ of $3{,}300$ new-set rows are filled, and $74.0\%$ are $5$. The 11-25-2026 6 PM PT wave and the 12-03-2026 wave are not in these files. Three added ratings did not shrink the experiment 25 intervals. The experiment 27 miss is $0.002$ on $20$ test tasks, and $35$ of $70$ test artifacts have two ratings. Later ratings stay on the same tasks; the $250$ interim was not used to refit or rescore that test. More ratings can tighten those histograms and intervals. They do not remove the old-set leniency (half a point for these two judges; nearly one $0$–$5$ point for the selected test judge), and a pooled correlation is still not a substitute for RPS, CE, and TVD.
