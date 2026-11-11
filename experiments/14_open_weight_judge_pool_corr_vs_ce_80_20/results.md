# Experiment 14 results: ② (pick by train correlation) versus ④ (pick by train cross-entropy) on a large open-weight judge pool

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/14_open_weight_judge_pool_corr_vs_ce_80_20/results.md>

**TLDR:** I scored the 75 expert-rated artifacts with 15 open-weight models x the three experiment-100 prompts on free mercury2 GPUs (vLLM, no paid API); 39 of the 45 judges gave usable scores (Phi-4-mini's three prompts gave no parseable scores, three more judges had too many unparseable answers and were dropped). These judges are much weaker than the old Sol/Opus ones (median Pearson with the human mean 0.06, 16 of 39 negative, best 0.41, versus 0.62 to 0.78), so the bigger pool is mostly noise and adding it makes every chooser worse than on the old five (RPS of the CE mixture 0.136 on the old five, 0.166 on old plus open). On the main metric RPS, repeated 80/20 task splits (1,000 splits, humans held out): on the combined pool ④ (CE-fit mixture) beats ② (correlation-fit mixture), ② minus ④ = +0.0405 [+0.0237, +0.0575], and on the open-only pool too (+0.0502 [+0.0238, +0.0754]); on the old five it was a tie (+0.0056 [-0.0059, +0.0181]). It is not a clean win for CE: with the best single judge instead of a mixture, ② beats ④ on the combined pool (-0.0317 [-0.0638, -0.0047]), and ② wins on rank correlations in most rows. Retrospective on sampled judge scores, one judge family, 25 tasks, 5 test tasks per split.

## ② minus ④, repeated 80/20 task splits (1,000 splits, 20 train / 5 test tasks, humans held out), with 95% task-bootstrap intervals

Lower is better for RPS (main), CE and TVD, so a positive difference means ④ (CE-fit) is better. For Spearman and Pearson (higher is better) a positive difference means ② (correlation-fit) is better. "Mixture" = weights on the simplex over the pool, "single" = best single judge by the train criterion.

### Old pool: the 5 cached frontier judges (GPT-6 Sol high, Claude Opus 5.5 max; H0/H1/H2 prompts) (5 judges)

| Comparison | RPS (main) | CE | TVD | Spearman | Pearson |
| --- | --- | --- | --- | --- | --- |
| ② Pearson mixture minus ④ CE mixture | +0.0056 [-0.0059, +0.0181] | +0.374 [+0.101, +0.693] | +0.012 [-0.012, +0.036] | +0.063 [+0.052, +0.073] | +0.013 [+0.000, +0.023] |
| ② Spearman mixture minus ④ CE mixture | +0.0429 [+0.0167, +0.0696] | +2.682 [+1.445, +4.008] | +0.090 [+0.028, +0.153] | +0.115 [+0.098, +0.132] | +0.034 [+0.014, +0.053] |
| ② best single minus ④ best single | -0.0254 [-0.0570, +0.0005] | -0.830 [-1.657, -0.182] | -0.054 [-0.102, -0.013] | +0.111 [+0.088, +0.136] | +0.106 [+0.084, +0.132] |

Mean test score of each chooser (RPS / CE / TVD / Spearman / Pearson):

| Chooser | RPS | CE | TVD | Spearman | Pearson |
| --- | --- | --- | --- | --- | --- |
| constant (train marginal) | 0.1836 | 1.852 | 0.682 | n/a | n/a |
| equal-weight mixture | 0.1496 | 5.431 | 0.531 | 0.608 | 0.703 |
| ② best single by train Pearson | 0.1797 | 8.104 | 0.600 | 0.719 | 0.750 |
| ② mixture maximizing train Pearson | 0.1419 | 5.787 | 0.522 | 0.669 | 0.730 |
| ② mixture maximizing train Spearman (random simplex search, 4,000 draws) | 0.1792 | 8.095 | 0.600 | 0.721 | 0.751 |
| ④ best single by train CE | 0.2051 | 8.934 | 0.654 | 0.609 | 0.644 |
| ④ mixture minimizing train CE | 0.1362 | 5.413 | 0.510 | 0.606 | 0.717 |

Optimizer certificate failures: 0. Mean RPS of ② Pearson mixture minus equal-weight mixture: -0.0077 [-0.0235, +0.0066]; ④ CE mixture minus equal-weight: -0.0133 [-0.0240, -0.0027]; ④ minus constant: -0.0473 [-0.0947, -0.0008].

### Open pool: only the open-weight judges (new, this experiment) (39 judges)

| Comparison | RPS (main) | CE | TVD | Spearman | Pearson |
| --- | --- | --- | --- | --- | --- |
| ② Pearson mixture minus ④ CE mixture | +0.0502 [+0.0238, +0.0754] | +2.336 [+1.367, +3.295] | +0.009 [-0.040, +0.053] | +0.189 [+0.163, +0.216] | +0.188 [+0.159, +0.219] |
| ② Spearman mixture minus ④ CE mixture | +0.0893 [+0.0586, +0.1212] | +6.927 [+5.648, +8.106] | +0.039 [-0.018, +0.093] | +0.075 [+0.038, +0.110] | +0.104 [+0.061, +0.147] |
| ② best single minus ④ best single | +0.0529 [+0.0137, +0.0911] | +1.118 [+0.318, +1.986] | +0.026 [-0.042, +0.090] | +0.097 [+0.058, +0.135] | +0.165 [+0.119, +0.210] |

Mean test score of each chooser (RPS / CE / TVD / Spearman / Pearson):

| Chooser | RPS | CE | TVD | Spearman | Pearson |
| --- | --- | --- | --- | --- | --- |
| constant (train marginal) | 0.1836 | 1.852 | 0.682 | n/a | n/a |
| equal-weight mixture | 0.3107 | 3.216 | 0.762 | -0.172 | -0.174 |
| ② best single by train Pearson | 0.3680 | 10.538 | 0.770 | 0.209 | 0.190 |
| ② mixture maximizing train Pearson | 0.3274 | 5.725 | 0.739 | 0.220 | 0.196 |
| ② mixture maximizing train Spearman (random simplex search, 4,000 draws) | 0.3666 | 10.316 | 0.770 | 0.109 | 0.115 |
| ④ best single by train CE | 0.3151 | 9.419 | 0.745 | 0.112 | 0.024 |
| ④ mixture minimizing train CE | 0.2773 | 3.389 | 0.731 | 0.031 | 0.009 |

Optimizer certificate failures: 4. Mean RPS of ② Pearson mixture minus equal-weight mixture: +0.0167 [-0.0023, +0.0368]; ④ CE mixture minus equal-weight: -0.0334 [-0.0490, -0.0162]; ④ minus constant: +0.0937 [+0.0184, +0.1633].

### Combined pool: old 5 plus open-weight judges (44 judges)

| Comparison | RPS (main) | CE | TVD | Spearman | Pearson |
| --- | --- | --- | --- | --- | --- |
| ② Pearson mixture minus ④ CE mixture | +0.0405 [+0.0237, +0.0575] | +1.292 [+0.623, +2.018] | +0.035 [-0.004, +0.073] | +0.031 [+0.014, +0.049] | -0.002 [-0.021, +0.016] |
| ② Spearman mixture minus ④ CE mixture | +0.0134 [-0.0235, +0.0498] | +5.475 [+4.187, +6.775] | +0.009 [-0.054, +0.070] | +0.152 [+0.131, +0.173] | +0.095 [+0.067, +0.119] |
| ② best single minus ④ best single | -0.0317 [-0.0638, -0.0047] | -0.915 [-1.765, -0.244] | -0.060 [-0.110, -0.017] | +0.125 [+0.100, +0.153] | +0.124 [+0.098, +0.151] |

Mean test score of each chooser (RPS / CE / TVD / Spearman / Pearson):

| Chooser | RPS | CE | TVD | Spearman | Pearson |
| --- | --- | --- | --- | --- | --- |
| constant (train marginal) | 0.1836 | 1.852 | 0.682 | n/a | n/a |
| equal-weight mixture | 0.2733 | 2.688 | 0.725 | 0.113 | 0.114 |
| ② best single by train Pearson | 0.1797 | 8.104 | 0.600 | 0.719 | 0.750 |
| ② mixture maximizing train Pearson | 0.2063 | 3.915 | 0.626 | 0.600 | 0.654 |
| ② mixture maximizing train Spearman (random simplex search, 4,000 draws) | 0.1793 | 8.098 | 0.600 | 0.721 | 0.752 |
| ④ best single by train CE | 0.2114 | 9.019 | 0.660 | 0.595 | 0.627 |
| ④ mixture minimizing train CE | 0.1658 | 2.623 | 0.591 | 0.569 | 0.657 |

Optimizer certificate failures: 3. Mean RPS of ② Pearson mixture minus equal-weight mixture: -0.0669 [-0.0950, -0.0405]; ④ CE mixture minus equal-weight: -0.1075 [-0.1429, -0.0742]; ④ minus constant: -0.0178 [-0.0687, +0.0306].

## Each judge on its own (all 75 artifacts, in-sample, no fitting)

Expected rating of each judge versus the human mean rating (Pearson, Spearman) and its forecast scores against the human rating distribution. A judge is one model x one prompt, three cached or sampled ratings per artifact.

| Judge | Source | RPS | CE | TVD | Spearman | Pearson | mean rating |
| --- | --- | --- | --- | --- | --- | --- | --- |
| H0_sol | cached frontier (Sol/Opus) | 0.1855 | 8.28 | 0.607 | 0.544 | 0.616 | 2.54 |
| H0_opus | cached frontier (Sol/Opus) | 0.2169 | 8.65 | 0.642 | 0.562 | 0.609 | 3.11 |
| H1_sol | cached frontier (Sol/Opus) | 0.1944 | 8.49 | 0.636 | 0.678 | 0.717 | 3.22 |
| H2_sol | cached frontier (Sol/Opus) | 0.1997 | 8.43 | 0.620 | 0.666 | 0.693 | 3.24 |
| H2_opus | cached frontier (Sol/Opus) | 0.1793 | 8.10 | 0.600 | 0.769 | 0.777 | 3.19 |
| glm4_9b_H0 | open-weight, vLLM, T=0.7 | 0.5064 | 12.30 | 0.918 | -0.433 | -0.585 | 3.75 |
| glm4_9b_H1 | open-weight, vLLM, T=0.7 | 0.4910 | 11.55 | 0.882 | -0.566 | -0.644 | 3.84 |
| glm4_9b_H2 | open-weight, vLLM, T=0.7 | 0.4430 | 11.18 | 0.822 | -0.035 | -0.017 | 4.84 |
| granite33_8b_H0 | open-weight, vLLM, T=0.7 | 0.3033 | 9.39 | 0.718 | 0.209 | 0.246 | 4.04 |
| granite33_8b_H2 | open-weight, vLLM, T=0.7 | 0.3333 | 9.40 | 0.760 | -0.209 | -0.163 | 4.10 |
| hermes3_8b_H0 | open-weight, vLLM, T=0.7 | 0.3210 | 9.47 | 0.702 | 0.256 | 0.178 | 4.16 |
| hermes3_8b_H1 | open-weight, vLLM, T=0.7 | 0.3176 | 9.62 | 0.724 | 0.358 | 0.312 | 4.19 |
| llama31_8b_H0 | open-weight, vLLM, T=0.7 | 0.3296 | 9.24 | 0.700 | 0.289 | 0.258 | 4.36 |
| llama31_8b_H1 | open-weight, vLLM, T=0.7 | 0.2939 | 8.81 | 0.718 | 0.207 | 0.062 | 3.89 |
| llama31_8b_H2 | open-weight, vLLM, T=0.7 | 0.3366 | 9.13 | 0.736 | -0.111 | -0.122 | 4.09 |
| mistral7b_v03_H0 | open-weight, vLLM, T=0.7 | 0.4092 | 11.13 | 0.851 | -0.072 | 0.066 | 4.50 |
| mistral7b_v03_H1 | open-weight, vLLM, T=0.7 | 0.3867 | 9.98 | 0.784 | -0.091 | 0.229 | 4.56 |
| mistral7b_v03_H2 | open-weight, vLLM, T=0.7 | 0.3129 | 9.71 | 0.776 | 0.285 | 0.204 | 3.96 |
| olmo3_7b_H0 | open-weight, vLLM, T=0.7 | 0.3935 | 10.83 | 0.791 | 0.198 | 0.211 | 4.56 |
| olmo3_7b_H1 | open-weight, vLLM, T=0.7 | 0.3887 | 10.60 | 0.778 | 0.307 | 0.345 | 4.62 |
| q25_7b_H0 | open-weight, vLLM, T=0.7 | 0.4033 | 10.64 | 0.796 | 0.021 | 0.046 | 4.64 |
| q25_7b_H1 | open-weight, vLLM, T=0.7 | 0.3665 | 10.15 | 0.756 | 0.270 | 0.194 | 4.41 |
| q25_7b_H2 | open-weight, vLLM, T=0.7 | 0.3662 | 10.07 | 0.787 | -0.029 | 0.030 | 4.41 |
| q25c_14b_H0 | open-weight, vLLM, T=0.7 | 0.4172 | 10.90 | 0.858 | -0.362 | -0.365 | 3.84 |
| q25c_14b_H1 | open-weight, vLLM, T=0.7 | 0.3819 | 10.05 | 0.802 | -0.274 | -0.247 | 3.96 |
| q25c_14b_H2 | open-weight, vLLM, T=0.7 | 0.3544 | 10.22 | 0.816 | -0.141 | -0.138 | 3.94 |
| q25c_7b_H0 | open-weight, vLLM, T=0.7 | 0.3535 | 10.29 | 0.813 | -0.160 | -0.139 | 3.36 |
| q25c_7b_H1 | open-weight, vLLM, T=0.7 | 0.3476 | 9.80 | 0.784 | -0.062 | -0.029 | 4.03 |
| q25c_7b_H2 | open-weight, vLLM, T=0.7 | 0.3938 | 10.74 | 0.844 | -0.211 | -0.291 | 3.52 |
| q3_14b_H0 | open-weight, vLLM, T=0.7 | 0.3677 | 11.03 | 0.822 | 0.130 | 0.200 | 4.28 |
| q3_14b_H1 | open-weight, vLLM, T=0.7 | 0.3001 | 10.24 | 0.758 | 0.164 | 0.144 | 3.59 |
| q3_14b_H2 | open-weight, vLLM, T=0.7 | 0.4121 | 10.33 | 0.769 | -0.249 | -0.409 | 3.76 |
| q3_30b_a3b_awq_H0 | open-weight, vLLM, T=0.7 | 0.4566 | 11.74 | 0.853 | 0.037 | 0.065 | 4.90 |
| q3_30b_a3b_awq_H1 | open-weight, vLLM, T=0.7 | 0.4548 | 11.92 | 0.862 | 0.087 | 0.059 | 4.91 |
| q3_30b_a3b_awq_H2 | open-weight, vLLM, T=0.7 | 0.4536 | 11.52 | 0.844 | 0.150 | 0.204 | 4.90 |
| q3_4b_2507_H0 | open-weight, vLLM, T=0.7 | 0.3973 | 10.83 | 0.798 | 0.141 | 0.071 | 3.66 |
| q3_4b_2507_H1 | open-weight, vLLM, T=0.7 | 0.4278 | 11.41 | 0.831 | 0.185 | 0.107 | 4.14 |
| q3_4b_2507_H2 | open-weight, vLLM, T=0.7 | 0.3416 | 10.48 | 0.764 | 0.390 | 0.407 | 4.35 |
| q3_8b_H0 | open-weight, vLLM, T=0.7 | 0.4284 | 11.83 | 0.887 | -0.031 | -0.055 | 2.64 |
| q3_8b_H1 | open-weight, vLLM, T=0.7 | 0.5265 | 12.78 | 0.942 | -0.254 | -0.338 | 3.31 |
| q3_8b_H2 | open-weight, vLLM, T=0.7 | 0.4821 | 11.34 | 0.858 | -0.381 | -0.383 | 4.21 |
| seed_coder_8b_H0 | open-weight, vLLM, T=0.7 | 0.4047 | 10.88 | 0.798 | 0.048 | 0.070 | 4.61 |
| seed_coder_8b_H1 | open-weight, vLLM, T=0.7 | 0.4151 | 10.56 | 0.798 | -0.001 | -0.087 | 4.52 |
| seed_coder_8b_H2 | open-weight, vLLM, T=0.7 | 0.3440 | 9.67 | 0.740 | 0.081 | 0.133 | 4.28 |

## Harness, models, hardware

- Harness: no agent harness. A plain script ([scripts/run_slot.py](scripts/run_slot.py)) calls a local vLLM 0.11.0 OpenAI-compatible server, one server per model, one chat request per (artifact, prompt) with 4 samples (temperature 0.7, top_p 0.95, max 700 new tokens); the first 3 parseable samples are the judge's three ratings. Prompts: the exact experiment-100 H0, H1, H2 renderers ([scripts/render.py](scripts/render.py) imports experiment 100's prompts.py), rendered from the veribench checkout (commit be287d9). Parsing: experiment 100's rule (one JSON object, integer final_score_0_5 in 0 to 5, no conflicting verdicts). Written and run by Brando's AI assistant; no LLM is in the selection loop.
- Open-weight judges (15 models, 3 prompts each, bf16 unless noted; Qwen3 with thinking switched off): Qwen2.5-7B-Instruct, Qwen2.5-Coder-7B-Instruct, Qwen2.5-Coder-14B-Instruct, Qwen3-4B-Instruct-2507, Qwen3-8B, Qwen3-14B, Qwen3-30B-A3B-Instruct-2507 (AWQ 4-bit, cpatonn), Llama-3.1-8B-Instruct (unsloth), Mistral-7B-Instruct-v0.3, Granite-3.3-8B-Instruct, Hermes-3-Llama-3.1-8B, GLM-4-9B-0414, Olmo-3-7B-Instruct, Seed-Coder-8B-Instruct, Phi-4-mini-instruct.
- Dropped judges (counted in results/judge_parse_stats.json): Phi-4-mini H0, H1, H2 (no or almost no parseable answers), Granite-3.3-8B H1, Hermes-3 H2, Olmo-3 H2 (more than 3 of 75 artifacts without any parseable answer). Five artifacts across three kept judges (Granite H0 1, Hermes H0 3, Llama-3.1 H0 1) had no parseable answer and were filled with that judge's own mean rating; no other filling.
- Nodes: mercury2 (10 x RTX A4000 16 GB, all free) did the work, 4 servers at a time, about 1 h 50 min wall. mercury1 had only GPUs 0 and 9 free, not used. skampere1 (A100) and skampere2 (H200) were fully busy with other jobs, not touched (skampere1 also runs the Exp 25 third seed). SNAP Slurm was not tried. Cost $0, no paid API, no key used.
- Judged object: LLM reading of spec coverage (the human-rater instructions), no Lean check and no DT in these judges; the human ratings are expert readings. Public-side artifacts: 75 candidate files from 3 Claude 3.7 Sonnet samples per task.
- Fitting: identical to experiment 12 (same split seeds 20261210 to 20262209, same estimators, same bootstrap), except the Pearson-maximizing mixture uses [scripts/nnls_pearson.py](scripts/nnls_pearson.py) (non-negative least squares on the same cone; experiment 3's face enumeration is capped at 8 judges) and the vendored input check cap was raised from 8 to 64. [scripts/check_nnls.py](scripts/check_nnls.py): same training Pearson as the enumeration solver on 200 five-judge splits (max difference 7e-16), and the old-pool rerun reproduces experiment 12's numbers exactly (RPS ② 0.14187, ④ 0.13624).

## Limits and what was not checked

- Weak judges: the open models were used as-is with the human-mirror prompts, at 3 samples each. They are poor judges here (see the per-judge table), so this tests selection among mostly bad judges, not among good open judges. Bigger or reasoning-mode open models, tuned prompts and logprob-based distributions were not tried.
- Small data: 25 tasks, 75 artifacts, 2 to 3 expert ratings each (195 in total), a split tests on only 5 tasks; the splits overlap, so intervals come from the task bootstrap.
- A larger pool gives the mixture more room to overfit 20 training tasks; the combined-pool result (④ beats ② on mixtures but worse than on the old five) mixes that with the weak-judge effect. Not separated.
- The old five judges' prompts were developed with the original train split's human ratings (see experiment 12), which may flatter the old pool. The open judges' prompts are those same prompts, so the same exposure applies.
- The Spearman-mixture chooser is a random search over the simplex (4,000 draws) and is weak in a 40-judge pool; read its rows with that in mind.
- Optimizer certificates failed in 4 of 1,000 splits (open pool) and 3 of 1,000 (combined pool); the old pool had 0. Those splits are kept in the averages.
- Fixed-split agents of experiment 12 were not rerun.
- One run of each sampled judge (temperature 0.7); repeat-to-repeat variation of the sampled scores was not measured.
- Human ratings are private and not committed; results/judge_scores.json holds judge scores only. Rebuild path: experiment 12's build_dataset.py (from the veribench checkout) for the human rows, then scripts/assemble.py with results/raw_judge_outputs.
