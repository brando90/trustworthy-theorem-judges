# Experiment 21 results: ② (pick by correlation) versus ④ (pick by cross-entropy) with a larger pool of frontier judges

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/21_add_3_frontier_judges_to_pool_pearson_vs_ce_80_20_start_16Nov2026/results.md>

**TLDR:** Three new frontier judges (gpt-6-astra, gpt-6.1-sol, gemini-4-argon) each scored the 75 artifacts 3 times (675 calls, about $20.2 at list prices; no Opus API route worked, so no new Opus judge). With all 8 judges in the pool, ② and ④ still tie on the main metric RPS over 1000 task splits: ② minus ④ = +0.0051 [-0.0034, +0.0136] (lower is better). ④ is better on CE (+0.739 [+0.304, +1.280]) and TVD (+0.0276 [+0.0048, +0.0507]); ② is better on Spearman (+0.079 [+0.071, +0.088]) and Pearson (+0.049 [+0.042, +0.057]). With gpt-6-astra as the optimizing agent on one fixed split, RPS ties again, ④ is better on CE, and ② has the higher test correlations (TVD interval includes zero; 5 test tasks only).

Method: identical to experiment 12 (80/20 task splits, 20 train tasks = 60 artifacts, 5 test tasks = 15 artifacts, 1,000 repeats from seed 20261210, 10,000-draw paired task bootstrap, a fixed split with seed 1210). A judge's distribution is the histogram of its 3 calls on the frozen H2 prompt, smoothed at 1e-6. ② maximizes the train Pearson (or Spearman) between the expected rating and the human mean; ④ minimizes train cross-entropy. Both search single judges and mixtures. Lower is better for RPS (main), CE and TVD; higher for Spearman and Pearson (secondary). Correlations need several test artifacts, so each split's test correlation is attributed to its 5 test tasks and averaged per task before the bootstrap. The human ratings are private and are not in this repository; `scripts/` reproduces everything given the private data.

## Pool: old 5 judges (GPT-6 Sol H0/H1/H2, Opus 5.5 H0/H2) — repeat of exp 12

Mean test score over the splits:

| Method | RPS (main) | CE | TVD | Spearman | Pearson |
| --- | --- | --- | --- | --- | --- |
| constant (train marginal) | 0.1836 | 1.852 | 0.6818 | n/a | n/a |
| equal-weight mixture | 0.1496 | 5.431 | 0.5311 | 0.608 | 0.703 |
| ② best single judge by train Pearson | 0.1797 | 8.104 | 0.6004 | 0.719 | 0.750 |
| ② mixture maximizing train Pearson | 0.1419 | 5.787 | 0.5222 | 0.669 | 0.730 |
| ② mixture maximizing train Spearman | 0.1792 | 8.095 | 0.5998 | 0.721 | 0.751 |
| ④ best single judge by train CE | 0.2051 | 8.934 | 0.6540 | 0.609 | 0.644 |
| ④ mixture minimizing train CE | 0.1362 | 5.413 | 0.5098 | 0.606 | 0.717 |

② minus ④ (paired 10,000-draw task bootstrap, 95% interval):

| Comparison | RPS (main) | CE | TVD | Spearman | Pearson |
| --- | --- | --- | --- | --- | --- |
| mixture ② (Pearson) − mixture ④ | +0.0056 [-0.0059, +0.0181] | +0.374 [+0.101, +0.693] | +0.0124 [-0.0123, +0.0363] | +0.063 [+0.052, +0.073] | +0.013 [+0.000, +0.023] |
| mixture ② (Spearman) − mixture ④ | +0.0429 [+0.0167, +0.0696] | +2.682 [+1.445, +4.008] | +0.0900 [+0.0279, +0.1533] | +0.115 [+0.098, +0.132] | +0.034 [+0.014, +0.053] |
| best single ② − best single ④ | -0.0254 [-0.0570, +0.0005] | -0.830 [-1.657, -0.182] | -0.0536 [-0.1022, -0.0131] | +0.111 [+0.088, +0.136] | +0.106 [+0.084, +0.132] |

Mean weights (candidate order H0_sol, H0_opus, H1_sol, H2_sol, H2_opus): ② Pearson mixture [0.291, 0.002, 0.0, 0.031, 0.675]; ④ mixture [0.389, 0.085, 0.102, 0.033, 0.391]. Single-judge picks (of 1,000 splits): ② {"H0_sol": 1, "H0_opus": 1, "H1_sol": 0, "H2_sol": 0, "H2_opus": 998}; ④ {"H0_sol": 313, "H0_opus": 6, "H1_sol": 3, "H2_sol": 77, "H2_opus": 601}.

## Pool: new 3 frontier judges only (Astra, Sol 6.1, Argon)

Mean test score over the splits:

| Method | RPS (main) | CE | TVD | Spearman | Pearson |
| --- | --- | --- | --- | --- | --- |
| constant (train marginal) | 0.1836 | 1.852 | 0.6818 | n/a | n/a |
| equal-weight mixture | 0.1746 | 7.583 | 0.5815 | 0.684 | 0.745 |
| ② best single judge by train Pearson | 0.1721 | 8.159 | 0.5978 | 0.768 | 0.797 |
| ② mixture maximizing train Pearson | 0.1693 | 7.735 | 0.5902 | 0.728 | 0.784 |
| ② mixture maximizing train Spearman | 0.1721 | 8.159 | 0.5978 | 0.768 | 0.797 |
| ④ best single judge by train CE | 0.1831 | 8.394 | 0.6128 | 0.735 | 0.757 |
| ④ mixture minimizing train CE | 0.1722 | 7.590 | 0.5834 | 0.695 | 0.751 |

② minus ④ (paired 10,000-draw task bootstrap, 95% interval):

| Comparison | RPS (main) | CE | TVD | Spearman | Pearson |
| --- | --- | --- | --- | --- | --- |
| mixture ② (Pearson) − mixture ④ | -0.0030 [-0.0126, +0.0034] | +0.145 [-0.020, +0.450] | +0.0068 [-0.0079, +0.0222] | +0.033 [+0.024, +0.048] | +0.034 [+0.025, +0.047] |
| mixture ② (Spearman) − mixture ④ | -0.0001 [-0.0127, +0.0100] | +0.569 [+0.062, +1.234] | +0.0144 [-0.0117, +0.0417] | +0.073 [+0.060, +0.091] | +0.046 [+0.033, +0.065] |
| best single ② − best single ④ | -0.0109 [-0.0246, -0.0012] | -0.235 [-0.459, -0.053] | -0.0150 [-0.0287, -0.0038] | +0.033 [+0.022, +0.047] | +0.039 [+0.026, +0.057] |

Mean weights (candidate order H2_astra, H2_sol61, H2_argon): ② Pearson mixture [0.02, 0.195, 0.784]; ④ mixture [0.344, 0.015, 0.641]. Single-judge picks (of 1,000 splits): ② {"H2_astra": 0, "H2_sol61": 0, "H2_argon": 1000}; ④ {"H2_astra": 73, "H2_sol61": 28, "H2_argon": 899}.

## Pool: all 8 judges

Mean test score over the splits:

| Method | RPS (main) | CE | TVD | Spearman | Pearson |
| --- | --- | --- | --- | --- | --- |
| constant (train marginal) | 0.1836 | 1.852 | 0.6818 | n/a | n/a |
| equal-weight mixture | 0.1528 | 5.086 | 0.5378 | 0.627 | 0.731 |
| ② best single judge by train Pearson | 0.1723 | 8.159 | 0.5979 | 0.768 | 0.796 |
| ② mixture maximizing train Pearson | 0.1390 | 5.827 | 0.5318 | 0.704 | 0.779 |
| ② mixture maximizing train Spearman | 0.1722 | 8.157 | 0.5977 | 0.768 | 0.796 |
| ④ best single judge by train CE | 0.2043 | 8.977 | 0.6551 | 0.627 | 0.656 |
| ④ mixture minimizing train CE | 0.1338 | 5.088 | 0.5042 | 0.624 | 0.730 |

② minus ④ (paired 10,000-draw task bootstrap, 95% interval):

| Comparison | RPS (main) | CE | TVD | Spearman | Pearson |
| --- | --- | --- | --- | --- | --- |
| mixture ② (Pearson) − mixture ④ | +0.0051 [-0.0034, +0.0136] | +0.739 [+0.304, +1.280] | +0.0276 [+0.0048, +0.0507] | +0.079 [+0.071, +0.088] | +0.049 [+0.042, +0.057] |
| mixture ② (Spearman) − mixture ④ | +0.0384 [+0.0160, +0.0612] | +3.069 [+1.854, +4.329] | +0.0935 [+0.0373, +0.1518] | +0.143 [+0.127, +0.161] | +0.066 [+0.053, +0.081] |
| best single ② − best single ④ | -0.0320 [-0.0614, -0.0081] | -0.818 [-1.498, -0.232] | -0.0573 [-0.0986, -0.0203] | +0.141 [+0.119, +0.165] | +0.140 [+0.119, +0.164] |

Mean weights (candidate order H0_sol, H0_opus, H1_sol, H2_sol, H2_opus, H2_astra, H2_sol61, H2_argon): ② Pearson mixture [0.244, 0.0, 0.0, 0.014, 0.023, 0.002, 0.014, 0.704]; ④ mixture [0.373, 0.042, 0.015, 0.006, 0.226, 0.17, 0.0, 0.167]. Single-judge picks (of 1,000 splits): ② {"H0_sol": 0, "H0_opus": 0, "H1_sol": 0, "H2_sol": 0, "H2_opus": 5, "H2_astra": 0, "H2_sol61": 0, "H2_argon": 995}; ④ {"H0_sol": 299, "H0_opus": 6, "H1_sol": 3, "H2_sol": 63, "H2_opus": 506, "H2_astra": 3, "H2_sol61": 2, "H2_argon": 118}.

## What the bigger pool changes (all 8 minus old 5, same splits, paired task bootstrap)

| Method | RPS | CE | TVD |
| --- | --- | --- | --- |
| ② mixture maximizing train Pearson | -0.0029 [-0.0136, +0.0048] | +0.040 [-0.210, +0.303] | +0.0096 [-0.0090, +0.0276] |
| ④ mixture minimizing train CE | -0.0024 [-0.0073, +0.0021] | -0.325 [-0.858, +0.065] | -0.0056 [-0.0210, +0.0081] |
| equal-weight mixture | +0.0032 [-0.0059, +0.0114] | -0.345 [-0.926, +0.057] | +0.0067 [-0.0178, +0.0302] |

A negative RPS or TVD change is an improvement. Every interval includes zero on RPS: the extra judges do not measurably help either method.

## Each judge alone against the human mean rating (all 75 artifacts, no fitting)

| Judge | Pearson | Spearman | mean abs error (0–1 scale) | mean RPS | mean CE |
| --- | --- | --- | --- | --- | --- |
| H0_sol | 0.616 | 0.548 | 0.192 | 0.1855 | 8.28 |
| H0_opus | 0.609 | 0.562 | 0.218 | 0.2169 | 8.65 |
| H1_sol | 0.717 | 0.680 | 0.196 | 0.1944 | 8.49 |
| H2_sol | 0.693 | 0.664 | 0.197 | 0.1997 | 8.43 |
| H2_opus | 0.777 | 0.769 | 0.176 | 0.1793 | 8.10 |
| H2_astra | 0.653 | 0.654 | 0.203 | 0.2071 | 8.50 |
| H2_sol61 | 0.773 | 0.722 | 0.188 | 0.1923 | 8.68 |
| H2_argon | 0.819 | 0.816 | 0.172 | 0.1721 | 8.16 |

These use all 75 artifacts, including those the split would hold out, and the prompt demos for the cached exp-100 judges came from the original train split (leakage caveat below), so they describe each judge, not generalization.

## One fixed split, frontier agent as optimizer

Test tasks: 18_MyFibonacci, 1_MyAdd, 3_heappop, bubble_sort, humaneval_13__gcd. Two gpt-6-astra agents (reasoning effort high, minimal custom tool loop with a python tool; see `agent/`) each got only the 60 train artifacts with all 8 judges' call histograms and the human ratings, and one instruction: ② maximize train Pearson, ④ minimize train cross-entropy over mixtures of the judges (plus the train marginal). They wrote a spec of weights; the scoring script applied it to the 15 test artifacts.

| Method | RPS (main) | CE | TVD | Spearman | Pearson |
| --- | --- | --- | --- | --- | --- |
| ② agent | 0.1155 | 4.915 | 0.4748 | 0.892 | 0.914 |
| ④ agent | 0.1197 | 1.494 | 0.4974 | 0.867 | 0.871 |
| ② coded optimizer (Pearson mixture) | 0.1155 | 4.915 | 0.4748 | 0.892 | 0.914 |
| ④ coded optimizer (CE mixture) | 0.1086 | 2.795 | 0.4198 | 0.816 | 0.857 |

Agent ② minus agent ④ (task bootstrap over the 5 test tasks): RPS -0.0042 [-0.0379, +0.0188], CE +3.421 [+2.564, +4.332], TVD -0.0226 [-0.0741, +0.0456]. Correlations over 15 artifacts are not bootstrapped. Weights: ② agent {"H0_sol": 0.309, "H2_argon": 0.691}; ④ agent {"H0_sol": 0.173, "H2_opus": 0.1, "H2_astra": 0.039, "H2_argon": 0.117, "train_marginal": 0.572}.

## Spend and what was not checked

- Judge calls: 675 (3 judges × 75 artifacts × 3 calls), all completed; about $10.82 (gpt-6-astra), $1.88 (gpt-6.1-sol), $7.53 (gemini-4-argon) = $20.23. Agents: $0.28. Total about $20.51 against the $300 cap. Computed from token usage times assumed list prices (Astra $10/$50, Sol 6.1 $2/$10, Argon $2/$10 per million tokens), not from provider billing. Earlier failed attempts (key probes, a Codex run that could not start) are not in this number.
- No Opus judge was added: no Anthropic API key or Vals route worked. The pool has the 2 cached Opus 5.5 judges only.
- Leakage: the cached exp-100 judges (H0/H1/H2) were built with prompts and demos that used the original train split's ratings. The three new judges use the same H2 prompt with leave-task-out rated demos, whose human ratings come from other tasks that can be test tasks in a given split, so the same caveat applies.
- Only 25 tasks (5 test tasks per split) and one fixed split for the agents; the agent comparison is anecdotal. The harness is a minimal custom loop with the OpenAI Responses API, not Codex.
