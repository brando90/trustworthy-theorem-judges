# Results: 5-metric evaluation (`RPS`, `CE`, `TVD`, `Pearson`, `Spearman`) of VeriBench theorem judges

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/22_evaluate_veribench_judges_on_75_outputs_distribution_losses_vs_correlations_start_16Nov2026/results.md>

**TLDR:** Re-scoring the cached `"0.6, 0.8, 0.8"` VeriBench selected judge (`H2_sol + H2_opus`: `openai/gpt-6-sol-high` + `anthropic/claude-opus-5-5-no-fallback`, Vals gateway, 6 calls/output, `no DT`, `$0` paid API calls) on the 5-metric panel shows that while its correlations jumped across `train / validation / test` (`Spearman = 0.6400, 0.8800, 0.8257`; `Pearson = 0.6576, 0.8601, 0.8578`), its **test Ranked Probability Score (`RPS`) degraded from validation (`0.1285`) to test (`0.1954 [0.1246, 0.2669]`) — worse than predicting the constant training marginal (`0.1836`, paired difference `+0.0118 [-0.0898, +0.1085]`, `p-val=0.8244`)** — because a `+0.1811 [+0.0989, +0.2622]` leniency bias (`55.0%` of its test mean squared error) is invisible to correlation. Across the 8-judge frontier pool (`H0/H1/H2 Sol/Opus` plus `gpt-6-astra`, `gpt-6.1-sol`, `gemini-4-argon`), `H0_sol` outperforms every `H2` single judge on test `RPS` (`0.1907` vs `0.1959–0.2078`) despite lower correlations (`0.664/0.591` vs `0.873/0.921`), and raw `④ RPS-trained` mixtures beat `② Pearson-trained` mixtures on canonical test `RPS` (`0.1443` vs `0.1693`, difference `+0.0250 [+0.0063, +0.0427]`, `p-val=0.0074`).

**Methodology & metric definitions:** See [EVAL_DOCUMENT_5_METRICS_11-16-2026.md](EVAL_DOCUMENT_5_METRICS_11-16-2026.md) · [Claude brief (`11-13-2026`)](https://claude.ai/artifact/Rg2hYLxYMGJAte7jcV7kKV) · [sister repository `judges-dont-need-psychometrics-or-corr`](https://github.com/brando90/judges-dont-need-psychometrics-or-corr).

---

## 1. Run scope, measurement contract, and consistency checks

- **What ran:** Central processing unit (CPU)-only post-hoc re-evaluation of cached large language model (LLM) judge integer scores (`0–5`) against the `195` expert human ratings across `75` candidate Lean formalizations (`25` Python tasks × `3` `claude-3-7-sonnet-20250219` samples) from `experiments/archive/01_veribench_25_tasks_3_samples_5_raters_judge_evaluation_start_03May2026_end_29Sep2026` (`source_commit = be287d9bb2f7bd35ba6db1b8735c9ba10d00eade`) combined with the 3 frontier judges (`H2_astra` [`gpt-6-astra` reasoning `high`, OpenAI Responses API], `H2_sol61` [`gpt-6.1-sol`, OpenAI Responses API], `H2_argon` [`gemini-4-argon`, Gemini `generateContent` API]) from `experiments/21_add_3_frontier_judges_to_pool_pearson_vs_ce_80_20_start_16Nov2026`.
- **Compute, proof status, and cost:** `0` new API calls, `$0.00` provider spend, **`no DT`** (no differential testing), **not** Lean-checked proofs (formal specification coverage [`FSC`] human-rating judgments only). All outputs are stored as split-level aggregates in [aggregates_5metrics.json](results/aggregates_5metrics.json); raw individual human ratings remain private and excluded by a programmatic guard.
- **Measurement contract & consistency verification:**
  1. Synthetic controls in [test_evaluate_5metrics.py](tests/test_evaluate_5metrics.py) (`5/5` passing): point mass on target gives `RPS=0, CE=0, TVD=0`; opposite-end miss gives `RPS=1.0, TVD=1.0, CE=+inf`; `3`-vs-`5` split gives identical mean (`0.80`) and correlations for `50/50` vs point-mass-`4`, while `RPS` separates them (`0.10` vs `0.20`); exact Pearson mean squared error (`MSE`) decomposition holds to `< 1e-13`; equal artifact weighting ignores variable rater count (`1` vs `3`).
  2. Exact receipt check against `exp100_TEST_RECEIPT.json` (`30` test items and `24` ordinary test items): maximum absolute discrepancy across `Spearman`, `Kendall tau-b`, `Pearson`, `ICC(A,1)`, `ICC(C,1)`, `MAE`, `mean_pred`, `mean_target`, and `mean_bias` is `1.11e-16` (`all_items`) and `3.33e-16` (`ordinary_items`).
  3. Exact canonical-split mixture cross-check against `experiments/archive/10_fit_5_judge_mixtures_to_75_outputs_pearson_vs_ranked_probability_start_09Nov2026_end_09Nov2026/results/results.json`: all `old5` `RPS`, `CE`, and `TVD` values match to `< 1e-12`.
- **Scalar convention note for Panel A:** `experiments/archive/01_veribench_25_tasks_3_samples_5_raters_judge_evaluation_start_03May2026_end_29Sep2026` (VeriBench experiment 100) defined its scalar score as the average of two 3-call member medians divided by 5 (`0.5 * (median(H2_sol) + median(H2_opus)) / 5`), whereas the 6-call probability distribution's expected score is the mean of all 6 calls divided by 5 (`mean6`). Both are reported below; `RPS`, `Cross-Entropy` (`CE`), and `Total Variation Distance` (`TVD`) use the 6-call probability histogram smoothed once at `eps = 1e-6`.
- **Uncertainty convention:** All confidence intervals (`CIs`) in Panels A and B are `95%` task-cluster percentile bootstrap intervals resampling whole tasks with replacement (`seed = 20260928`, `10,000` draws for `train`, `val`, `test`, `all_75`; `2,000` draws for `test_ordinary` matching `exp100_TEST_RECEIPT.json`, cross-checked at `10,000` draws). All p-values compare `judge minus baseline` via paired task bootstrap against zero difference (`p-val=n/a` for single-model standalone metrics).

---

## 2. Panel A — Re-evaluating the `"0.6, 0.8, 0.8"` VeriBench judge across splits

Selected judge (`test_H2_sol_plus_H2_opus`, Vals gateway): `openai/gpt-6-sol-high` (reasoning `high`) + `anthropic/claude-opus-5-5-no-fallback` (compute effort `max`, adaptive thinking), `H2` prompt, 3 calls per member = 6 calls/output. Baseline: `constant` out-of-sample training-marginal distribution (`train` empirical human PMF smoothed at `eps = 1e-6`).

| Split (`outputs / tasks / ratings`) | `RPS` (primary, ↓) | `Constant RPS` | `CE` (`eps=1e-6`, ↓) | `Constant CE` | `TVD` (↓) | `Pearson r` (↑) | `Spearman rho` (↑) | `MAE` `[0,1]` (↓) | `Signed bias` `[0,1]` (`judge / human`) | `ICC(A,1)` / `ICC(C,1)` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `train` (`30 / 10 / 78`) | `0.1793` `[0.1176, 0.2550]` | `0.1736` | `7.994` `[6.488, 9.746]` | `1.743` | `0.5833` `[0.4778, 0.7056]` | `0.6576` `[0.1563, 0.9235]` | `0.6400` `[0.2441, 0.9074]` | `0.1778` `[0.1156, 0.2534]` | `+0.0733` (`0.6367 / 0.5633`) | `0.6448 / 0.6564` |
| `val` (`15 / 5 / 39`) | `0.1285` `[0.0556, 0.2074]` | `0.1668` | `5.467` `[1.730, 9.219]` | `1.777` | `0.5000` `[0.2333, 0.7444]` | `0.8601` `[0.7701, 0.9955]` | `0.8800` `[0.6961, 0.9990]` | `0.1378` `[0.0622, 0.2133]` | `+0.0978` (`0.6533 / 0.5556`) | `0.8216 / 0.8570` |
| **`test` (`30 / 10 / 78`)** | **`0.1954`** `[0.1246, 0.2669]` | **`0.1836`** | `8.309` `[5.978, 10.618]` | `1.805` | `0.6278` `[0.4778, 0.7778]` | `0.8578` `[0.7068, 0.9412]` | `0.8257` `[0.3162, 0.9656]` | `0.2011` `[0.1300, 0.2733]` | **`+0.1811`** (`0.6533 / 0.4722`) | `0.7273 / 0.8515` |
| `test_ordinary` (`24 / 8 / 66`) | **`0.2234`** `[0.1405, 0.2965]` | **`0.1783`** | `8.948` `[6.184, 11.545]` | `1.838` | `0.6806` `[0.5069, 0.8472]` | `0.8347` `[0.4537, 0.9579]` | `0.6519` `[-0.1662, 0.9161]` | `0.2306` `[0.1472, 0.3042]` | **`+0.2056`** (`0.5667 / 0.3611`) | `0.5798 / 0.7605` |
| `all_75` (`75 / 25 / 195`) | `0.1756` `[0.1333, 0.2206]` | `0.1762` | `7.615` `[6.198, 9.053]` | `1.774` | `0.5844` `[0.4911, 0.6800]` | `0.7657` `[0.5714, 0.8905]` | `0.7578` `[0.5467, 0.8961]` | `0.1791` `[0.1364, 0.2245]` | `+0.1213` (`0.6467 / 0.5253`) | `0.7079 / 0.7633` |

*Notes:* Scalar metrics in the table use Experiment 100's member-median average (`0.5*(median(H2_sol)+median(H2_opus))/5`). Using the 6-call distribution mean (`mean6`) gives nearly identical values on `test`: `Pearson = 0.8571`, `Spearman = 0.8179`, `Kendall tau-b = 0.6779` (vs `0.6982`), `MAE = 0.1978`, `signed bias = +0.1800`, `ICC(A,1) = 0.7276`. Checking `test_ordinary` with `10,000` bootstrap draws instead of `2,000` gives `RPS = 0.2234 [0.1410, 0.2972]` and `Spearman = 0.6519 [-0.1657, +0.9149]`.

### Paired comparisons against the constant training marginal (`judge minus constant`, `p-val` from paired task bootstrap)

- **`train`**: `RPS` `+0.0057 [-0.0765, +0.0921]`, `p-val=0.9032`; `CE` `+6.2512 [+4.7276, +8.0188]`, `p-val=0.0001`; `TVD` `-0.0704 [-0.1939, +0.0639]`, `p-val=0.2898`.
- **`val`**: `RPS` `-0.0383 [-0.1507, +0.0406]`, `p-val=0.5644`; `CE` `+3.6903 [-0.0212, +7.4018]`, `p-val=0.0572`; `TVD` `-0.1948 [-0.5411, +0.0633]`, `p-val=0.2064`.
- **`test`**: `RPS` **`+0.0118 [-0.0898, +0.1085]`, `p-val=0.8244`** (worse than constant point estimate); `CE` `+6.5044 [+4.1264, +8.8522]`, `p-val=0.0001`; `TVD` `-0.0372 [-0.2091, +0.1256]`, `p-val=0.6640`.
- **`test_ordinary`**: `RPS` **`+0.0451 [-0.0771, +0.1511]`, `p-val=0.4570`**; `CE` `+7.1102 [+4.2146, +9.7384]`, `p-val=0.0005`; `TVD` `+0.0086 [-0.1896, +0.1934]`, `p-val=0.9280`.
- **`all_75`**: `RPS` `-0.0007 [-0.0575, +0.0556]`, `p-val=0.9704`; `CE` `+5.8403 [+4.4139, +7.2843]`, `p-val=0.0001`; `TVD` `-0.0820 [-0.1907, +0.0222]`, `p-val=0.1234`.

### Why `"0.6, 0.8, 0.8"` behaved so strangely (Pearson `MSE` decomposition)

| Split | Total `MSE` `[0,1]` (`nRMSE`) | `Bias^2` (`share`) | `Scale mismatch^2` (`share`, `judge SD / human SD`) | `2 s_x s_y (1 - r)` (`share`, what `Pearson` sees) |
| --- | ---: | ---: | ---: | ---: |
| `train` (`30`) | `0.0660` (`0.2569`) | `0.0054` (`8.2%`) | `0.0003` (`0.5%`, `0.306 / 0.288`) | `0.0603` (`91.3%`) |
| `val` (`15`) | `0.0338` (`0.1838`) | `0.0096` (`28.3%`) | `0.0006` (`1.8%`, `0.303 / 0.279`) | `0.0236` (`69.9%`) |
| **`test` (`30`)** | `0.0596` (`0.2441`) | **`0.0328` (`55.0%`)** | `0.0013` (`2.2%`, `0.318 / 0.282`) | `0.0255` (`42.7%`) |
| **`test_ordinary` (`24`)** | `0.0724` (`0.2691`) | **`0.0423` (`58.4%`)** | **`0.0112` (`15.5%`, `0.298 / 0.192`)** | `0.0190` (`26.2%`) |

**Takeaway:** Under `RPS`, `val` (`0.1285`) -> `test` (`0.1954`) -> `test_ordinary` (`0.2234`) shows ordinary validation optimism followed by severe out-of-sample degradation. `Pearson` missed this completely because `55.0%` of test `MSE` (`73.8%` on ordinary test items!) is bias + scale mismatch, which `Pearson` discards, while two placeholder-reference test tasks inflated `Spearman` (`0.6519 -> 0.8257`).

### Probability-floor sensitivity (`Panel A`, 6-call empirical PMF)

| Split | `RPS` (`eps=1e-6` / `1e-3` / `Laplace 0.5`) | `CE` (`eps=1e-6` / `1e-3` / `Laplace 0.5`) | `TVD` (`eps=1e-6` / `1e-3` / `Laplace 0.5`) |
| --- | ---: | ---: | ---: |
| `train` (`30`) | `0.1793 / 0.1782 / 0.1407` | `7.994 / 4.046 / 1.870` | `0.5833 / 0.5829 / 0.5611` |
| `val` (`15`) | `0.1285 / 0.1278 / 0.1050` | `5.467 / 2.939 / 1.600` | `0.5000 / 0.5007 / 0.5333` |
| `test` (`30`) | `0.1954 / 0.1941 / 0.1466` | `8.309 / 4.208 / 1.934` | `0.6278 / 0.6270 / 0.5852` |
| `test_ordinary` (`24`) | `0.2234 / 0.2220 / 0.1655` | `8.948 / 4.539 / 2.069` | `0.6806 / 0.6796 / 0.6273` |

With 6 discrete calls, `CE` moves by **4+ nats** based solely on the zero-bin smoothing floor (`1e-6` vs `1e-3` vs `Laplace(0.5)`), whereas `RPS` changes by only `0.0012` between `1e-6` and `1e-3` (and even `Laplace(0.5)` keeps identical split ordering).

---

## 3. Panel B — All 8 single frontier judges & mixtures on the canonical `10 / 5 / 10` split

### Single judges (`3` calls per artifact, `eps = 1e-6`, `no DT`, `test n = 30 / 10 tasks`, `p-val=n/a`)

| Judge (`model`, `harness`, `effort`) | `Val RPS` | `Test RPS` `[95% CI]` (↓) | `Test CE` (↓) | `Test TVD` (↓) | `Test Pearson` (↑) | `Test Spearman` (↑) | `Test bias` (`judge / human`) | `Ord Test RPS` (`24`) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **`constant_train_marginal`** | `0.1668` | **`0.1836`** `[0.1424, 0.2277]` | **`1.805`** | `0.6650` | `n/a` | `n/a` | `+0.091` (`0.563 / 0.472`) | **`0.1783`** |
| `H0_sol` (`gpt-6-sol-high`, Vals, `high`) | `0.1052` | **`0.1907`** `[0.1400, 0.2448]` | `9.133` | `0.6722` | `0.664` | `0.591` | **`+0.014`** (`0.487 / 0.472`) | **`0.2046`** |
| `H2_opus` (`claude-opus-5-5-no-fallback`, Vals, `max`) | `0.1333` | `0.1959` `[0.1274, 0.2652]` | `8.710` | `0.6389` | `0.862` | `0.840` | `+0.177` (`0.649 / 0.472`) | `0.2241` |
| `H2_argon` (`gemini-4-argon`, Gemini API) | `0.1348` | `0.1989` `[0.1300, 0.2667]` | `8.702` | `0.6389` | `0.873` | **`0.921`** | `+0.177` (`0.649 / 0.472`) | `0.2278` |
| `H2_astra` (`gpt-6-astra`, Responses API, `high`) | `0.1585` | `0.2011` `[0.1263, 0.2781]` | `8.021` | **`0.6167`** | `0.849` | `0.852` | `+0.166` (`0.638 / 0.472`) | `0.2306` |
| `H2_sol` (`gpt-6-sol-high`, Vals, `high`) | `0.1852` | `0.2033` `[0.1304, 0.2770]` | `8.446` | `0.6278` | `0.840` | `0.811` | `+0.183` (`0.656 / 0.472`) | `0.2333` |
| `H2_sol61` (`gpt-6.1-sol`, Responses API) | `0.1911` | `0.2078` `[0.1363, 0.2807]` | `8.937` | `0.6500` | `0.840` | `0.809` | `+0.170` (`0.642 / 0.472`) | `0.2389` |
| `H1_sol` (`gpt-6-sol-high`, Vals, `high`) | `0.1704` | `0.2122` `[0.1474, 0.2770]` | `9.123` | `0.6667` | `0.799` | `0.767` | `+0.177` (`0.649 / 0.472`) | `0.2426` |
| `H0_opus` (`claude-opus-5-5-no-fallback`, Vals, `max`) | `0.1556` | `0.2730` `[0.1804, 0.3826]` | `10.374` | `0.7500` | `0.582` | `0.659` | `+0.188` (`0.660 / 0.472`) | `0.3204` |

**Key Panel B single-judge finding:** Every single 3-call judge loses to `constant_train_marginal` (`0.1836`) on test `RPS`, and `H0_sol` (`0.1907`) beats *every* `H2` frontier judge (`0.1959–0.2078`) on test `RPS` despite having much lower `Pearson` (`0.664`) and `Spearman` (`0.591`) than `H2_argon` (`0.873`, `0.921`). Notice also that all 3 new frontier judges (`H2_astra`, `H2_sol61`, `H2_argon`) inherit the `+0.166` to `+0.177` leniency bias of the `H2` prompt!

### Trained simplex mixtures on `old5` and `all8` pools (`10 / 5 / 10` canonical split, `test n = 30`)

Here `raw` sets shrinkage `lambda = 0.0` (pure simplex mixture over base judges), while `val_rps_shrink` picks `lambda in {0.0, 0.05, 0.10, 0.25, 0.50, 1.0}` toward `constant_train_marginal` using validation `RPS` (`n = 15`, 5 tasks).

| Pool & Method (`lambda`) | `Val RPS` | `Test RPS` `[95% CI]` (↓) | `Test CE` (↓) | `Test TVD` (↓) | `Test Pearson` (↑) | `Test Spearman` (↑) | `Test bias` (`[0,1]`) | `Ord Test RPS` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `old5`: `equal_mixture` (`0.0`) | `0.1044` | `0.1729` `[0.1253, 0.2200]` | `6.918` | `0.5967` | `0.813` | `0.824` | `+0.148` | `0.1953` |
| `old5`: `② pearson_raw` (`0.0`) | `0.0861` | `0.1563` `[0.1102, 0.2044]` | `7.119` | `0.5783` | `0.860` | `0.832` | `+0.133` | `0.1747` |
| `old5`: `④ ce_raw` (`0.0`) | `0.0800` | `0.1608` `[0.1206, 0.2002]` | `6.902` | `0.5866` | `0.810` | `0.800` | `+0.127` | `0.1797` |
| `old5`: `④ rps_raw` (`0.0`) | `0.0741` | `0.1502` `[0.1119, 0.1891]` | `6.907` | `0.5735` | `0.835` | `0.824` | `+0.115` | `0.1663` |
| `old5`: `② pearson + val_rps_shrink` (`0.25`) | `0.0817` | `0.1375` `[0.0998, 0.1755]` | `1.924` | `0.5598` | `0.860` | `0.832` | `+0.123` | `0.1549` |
| `old5`: `④ rps + val_rps_shrink` (`0.10`) | `0.0733` | `0.1427` `[0.1052, 0.1802]` | `2.320` | `0.5638` | `0.836` | `0.831` | `+0.115` | `0.1594` |
| `all8`: `equal_mixture` (`0.0`) | `0.1130` | `0.1733` `[0.1170, 0.2298]` | `6.221` | `0.5861` | `0.849` | `0.830` | `+0.156` | `0.1962` |
| `all8`: `② pearson_raw` (`0.0`) | `0.1049` | `0.1693` `[0.1152, 0.2256]` | `7.285` | `0.6081` | **`0.885`** | **`0.851`** | `+0.152` | `0.1913` |
| `all8`: `④ ce_raw` (`0.0`) | `0.0800` | `0.1517` `[0.1111, 0.1946]` | `6.551` | `0.5718` | `0.853` | `0.829` | `+0.126` | `0.1687` |
| `all8`: `④ rps_raw` (`0.0`) | `0.0779` | **`0.1443`** `[0.1053, 0.1868]` | `6.730` | `0.5672` | `0.875` | `0.848` | **`+0.117`** | **`0.1591`** |
| `all8`: `② pearson + val_rps_shrink` (`0.25`) | `0.0912` | `0.1429` `[0.1008, 0.1871]` | **`1.968`** | `0.5770` | **`0.885`** | **`0.851`** | `+0.137` | `0.1622` |
| `all8`: `④ ce + val_rps_shrink` (`0.10`) | `0.0781` | `0.1428` `[0.1040, 0.1832]` | `2.238` | `0.5632` | `0.855` | `0.829` | `+0.122` | `0.1600` |
| **`all8`: `④ rps + val_rps_shrink` (`0.10`)** | `0.0767` | **`0.1372`** `[0.0994, 0.1777]` | `2.269` | **`0.5581`** | `0.878` | `0.848` | **`+0.116`** | **`0.1527`** |

- **Weights learned on `all8` (`train n = 30`, `val_rps_shrink`):**
  - `② pearson`: `0.846 H2_argon + 0.154 H0_sol` (shrinkage `0.25`).
  - `④ ce`: `0.316 H0_sol + 0.104 H0_opus + 0.233 H2_opus + 0.101 H2_sol61 + 0.247 H2_argon` (shrinkage `0.10`).
  - `④ rps`: `0.354 H0_sol + 0.135 H2_opus + 0.511 H2_argon` (shrinkage `0.10`).
- **Paired canonical test contrasts (`method2 minus method4`, fixed-prediction task bootstrap over 10 test tasks — note these do not include training/selection refit variance):**
  - On **`all8` raw** (`lambda = 0.0`): `② pearson_raw minus ④ rps_raw` has `RPS = +0.0250 [+0.0063, +0.0427]` (`p-val=0.0074`, **④ wins clearly**), `CE = +0.5554 [-0.0468, +1.6063]` (`p-val=0.161`), `TVD = +0.0409 [-0.0062, +0.0947]` (`p-val=0.0998`), `Pearson = +0.0100 [-0.0367, +0.1163]` (`p-val=0.645`), `Spearman = +0.0032 [-0.0152, +0.0279]` (`p-val=1.0`). Similarly `② pearson_raw minus ④ ce_raw` gives `RPS = +0.0177 [-0.0007, +0.0349]` (`p-val=0.0586`).
  - With `val_rps_shrink` (where validation `RPS` rescues `②` by selecting `lambda = 0.25` vs `0.10`), on `all8` `② minus ④_rps` narrows to `RPS = +0.0056 [-0.0017, +0.0128]` (`p-val=0.138`), and on `old5` `experiments/archive/10_fit_5_judge_mixtures_to_75_outputs_pearson_vs_ranked_probability_start_09Nov2026_end_09Nov2026`'s full refit/reselection task-family bootstrap gives `method4_rps minus method2_pearson = +0.0052 [-0.0681, +0.0149]` (`p-val=n/a`, unresolved).

---

## 4. Panel C — Repeated `1,000`-split `20 / 5` summary (from `experiments/21_...`)

To separate single-split noise (`10` test tasks) from systematic behavior across splits, `experiments/21_add_3_frontier_judges_to_pool_pearson_vs_ce_80_20_start_16Nov2026` averaged `1,000` random task-grouped `20 train / 5 test` splits (`seed = 20261210`, `10,000`-draw paired task bootstrap, no shrinkage):

| Pool & Method (`1,000` `20/5` splits) | Mean test `RPS` (↓) | Mean test `CE` (↓) | Mean test `TVD` (↓) | Mean test `Pearson` (↑) | Mean test `Spearman` (↑) |
| --- | ---: | ---: | ---: | ---: | ---: |
| `constant` (`train marginal`) | `0.1836` | **`1.852`** | `0.6818` | `n/a` | `n/a` |
| `old5`: `② mixture (train Pearson)` | `0.1419` | `5.787` | `0.5222` | `0.730` | `0.669` |
| `old5`: `④ mixture (train CE)` | `0.1362` | `5.413` | `0.5098` | `0.717` | `0.606` |
| `all8`: `② mixture (train Pearson)` | `0.1390` | `5.827` | `0.5318` | **`0.779`** | **`0.704`** |
| `all8`: `④ mixture (train CE)` | **`0.1338`** | `5.088` | **`0.5042`** | `0.730` | `0.624` |

- **Paired difference `all8` `② minus ④` (`1,000` splits, `10,000`-draw task bootstrap, `p-val=n/a`):**
  - `RPS`: `+0.0051 [-0.0034, +0.0136]` (tie on `RPS`),
  - `CE`: **`+0.739 [+0.304, +1.280]`** (`④` clearly better),
  - `TVD`: **`+0.0276 [+0.0048, +0.0507]`** (`④` clearly better),
  - `Spearman`: **`+0.079 [+0.071, +0.088]`** (`②` clearly higher),
  - `Pearson`: **`+0.049 [+0.042, +0.057]`** (`②` clearly higher).

---

## 5. Limitations

1. **Retrospective, prior-exposed corpus:** All `75` outputs come from one older generation distribution (`claude-3-7-sonnet-20250219`, temperature `0.7`, single-call, no compiler loop) with `195` expert ratings across `25` tasks (`19` task families), and `H0–H2` prompts/demos used labels from this same dataset (`experiments/archive/01_veribench_25_tasks_3_samples_5_raters_judge_evaluation_start_03May2026_end_29Sep2026`).
2. **Sampled discrete histograms, not native six-probability forecasts:** Each base judge has only `3` sampled integer ratings (`0–5`), creating sparse histograms whose raw `CE` depends strongly on `eps = 1e-6` vs `1e-3`. Fresh native six-probability evaluation requires the ongoing collection in `experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026` and the native scaffold in `experiments/02_design_a_judge_that_predicts_human_ratings_0_to_5_start_06Nov2026`.
3. **Small split counts & fixed-prediction CIs:** The canonical `test` split has only `10` tasks (`8` ordinary), and the canonical `Panel B` CIs condition on the fitted mixture weights rather than refitting inside each bootstrap resample (whereas Experiment 10 and Experiment 21 include refitting/re-splitting).

**TLDR-end:** [ttj: experiments/22_evaluate_veribench_judges_on_75_outputs_distribution_losses_vs_correlations_start_16Nov2026] Re-evaluating the `"0.6, 0.8, 0.8"` VeriBench judge (`H2_sol + H2_opus`) on all 5 metrics exposes a `+0.1811` test leniency bias (`55.0%` of test `MSE`) and worse-than-constant test `RPS` (`0.1954` vs `0.1836`), while showing across 8 frontier judges that raw `④ RPS` mixtures beat `② Pearson` mixtures on canonical test `RPS` (`0.1443` vs `0.1693`, `p-val=0.0074`).
