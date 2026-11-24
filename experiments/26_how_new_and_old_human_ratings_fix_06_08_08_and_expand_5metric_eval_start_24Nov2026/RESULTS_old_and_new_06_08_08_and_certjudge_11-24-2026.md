# Old and new VeriBench human ratings: correlation limitations and 5-metric evaluation — 11-24-2026

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/26_how_new_and_old_human_ratings_fix_06_08_08_and_expand_5metric_eval_start_24Nov2026/RESULTS_old_and_new_06_08_08_and_certjudge_11-24-2026.md>

**TLDR:** Live `11-24-2026` syncing of `33` Google Sheets in `09_prepare_packets_and_collect_human_ratings_start_28Sep2026` yields `247` numeric human ratings covering all `100` frontier candidate files across `25` distinct task IDs (`>=2` raters per file). Combining this frontier-quality cohort (`mean = 0.9143` artifact-equal) with the historical cohort in `01_veribench_25_tasks_3_samples_5_raters_judge_evaluation_start_03May2026_end_29Sep2026` (`mean = 0.5253`) supports a **stratified evaluation design using proper scoring rules (`RPS`, `CE`) and distribution discrepancy (`TVD`)**; frozen-judge evaluation on the new cohort remains pending — never via naive pooling (which induces between-cohort `Pearson = 0.6557` / `Spearman = 0.6594` from constant predictions with undefined within-regime correlations) and never via correlation alone (`91.50%` of new ratings are `4` or `5`). For `brando90/cert-judge`, `C_ms_gold` (`n = 16` held-out test judge configurations) has a higher point correlation with `-RPS` than with the saved Spearman criterion (the difference was not tested) (`r_s = 0.6078 [0.1282, 0.8659]` against `-RPS`, `p-val = 0.0077` permutation test), whereas `TI_var_trainnorm` fails (`r_s = -0.2782`) and `PTI_v0_frozen` collapses to zero on most configurations (`$0.00` API spend, CPU-only, `no DT`, not Lean-checked proofs).

**Date:** `11-24-2026`
**As of 11-24-2026:** Retrospective descriptive analysis; frozen-judge evaluation on the new cohort remains pending.

## 1. Executive Q1 answers (for reviewers and defense examiners)

### Question 1A (`brando90/trustworthy-theorem-judges`): How do new + old human ratings fix the `"0.6, 0.8, 0.8"` issue and widen evaluation beyond correlations?

**Acronyms expanded on first use:** Formal Specification Coverage (`FSC`), Ranked Probability Score (normalized 0–1, `RPS`), Cross-Entropy (`CE`), Total Variation Distance (`TVD`), Mean Absolute Error (`MAE`), Normalized Root Mean Squared Error (`NRMSE`), Mean Squared Error (`MSE`), Intraclass Correlation Coefficient absolute agreement (`ICC(A,1)`) and consistency (`ICC(C,1)`), Leave-One-Rater-Out (`LORO`), Probability Mass Function (`PMF`), Cumulative Distribution Function (`CDF`), Confidence Interval (`CI`), Differential Testing (`DT`), Proxy Trust Index (`PTI`), Trust Index variance (`TI_var`), multi-sample gold-reference consistency (`C_ms_gold`). Signed bias is always `judge - human` (or `predicted rater - target rater`), reported alongside both group means.

The following retrospective findings come from [summary_old_vs_new_11-24-2026.json](results/summary_old_vs_new_11-24-2026.json). Pairwise and leave-one-rater-out agreement are empirical comparison references, not upper bounds on judge performance; the empirical disagreement term is not a known population noise floor. New-cohort quality and independence remain subject to the listed attestation and response anomalies. Historical Experiment 41 and Experiment 51 claims below are carried forward from the saved summary and were not independently re-read during this scoped review. A zero placeholder count and nonempty theorem declarations do not establish semantic correctness of the references.

1. **Limitations of `"0.6, 0.8, 0.8"` on the old cohort (`75` artifacts, `25` tasks):** As measured in `22_evaluate_veribench_judges_on_75_outputs_distribution_losses_vs_correlations_start_16Nov2026`, the old Experiment 100 selected judge achieved split Spearman rank correlations of `0.6400 [0.2441, 0.9074]` on `train` (`10` tasks, `30` files), `0.8800 [0.6961, 0.9990]` on `val` (`5` tasks, `15` files), and `0.8257 [0.3162, 0.9656]` on `test` (`10` tasks, `30` files), with Pearson linear correlations of `0.6576 [0.1563, 0.9235]`, `0.8601 [0.7701, 0.9955]`, and `0.8578 [0.7068, 0.9412]` (`10,000` task-cluster bootstrap draws). Yet on the primary proper scoring rule `RPS`, that very judge **had a higher point loss than a constant train-marginal baseline on `test`, with an inconclusive paired difference**: `RPS = 0.1954 [0.1246, 0.2669]` versus constant `0.1836 [0.1424, 0.2277]` (paired difference `+0.0118 [-0.0898, +0.1085]`, `p-val = 0.8244` two-sided paired task-cluster bootstrap; `train` paired difference `+0.0057 [-0.0765, +0.0921]`, `p-val = 0.9032`). On `test`, `55.04%` of the judge's `MSE` came from level inflation (`signed_bias = +0.1811 [+0.0989, +0.2622]`, `judge mean = 0.6533` versus `human mean = 0.4722`), and `9` of `25` tasks had reference drift (`5` placeholder references in VeriBench Experiment 100).
2. **Expanding tasks from `k = 10` to `k = 25` shrinks task-cluster CI half-widths by ~`35%`:** Resampling `10` versus `25` whole tasks across `10,000` bootstrap draws on the live Experiment 09 human agreement reference (`T08` predicting `T05`) reduces `95%` CI half-widths from `0.0475` to `0.0310` (`0.6526x`) on `RPS`, `0.2741` to `0.1859` (`0.6783x`) on Spearman, `0.2066` to `0.0994` (`0.4809x`) on Pearson, and `0.2539` to `0.1692` (`0.6664x`) on Kendall tau-b. On the `theorem_count_ratio` baseline, half-width ratios range from about `0.63x` to `0.72x` (`RPS` `0.0604 -> 0.0384`, Spearman `0.3819 -> 0.2427`, Kendall `0.3508 -> 0.2198`, Pearson `0.3884 -> 0.2809`). This resampling sensitivity check uses the same observed 25-task cohort at both sample sizes. It does not measure new-judge generalization, establish that the historical validation correlation was luck, or guarantee narrower intervals on future tasks.
3. **Why new ratings alone cannot rely on correlation — and why old + new together require proper distributional losses:** In `09_prepare_packets_and_collect_human_ratings_start_28Sep2026`, `4` frontier native agents replace single-call `claude-3-7-sonnet-20250219`, shifting human ratings to `mean = 0.9143` artifact-equal (`91.50%` of the `247` ratings are `4` or `5`). Under this near-ceiling range restriction, the complete-overlap human pair (`T08` Amy Lu versus `T05` Srivatsava Daruru across all `100` files, `100%` within-1 agreement, quadratic Cohen's kappa `0.7496`, `RPS = 0.0760 [0.0460, 0.1080]`, Pearson `0.8285 [0.6895, 0.8882]`) has Spearman only `0.6243 [0.4035, 0.7754]` and Kendall `0.5995 [0.3958, 0.7342]` in a sample with heavy ties at `5`; this does not isolate the cause of the difference between correlation metrics. Worse, on the `16` shared items rated by `T06` (all `5`), Spearman, Pearson, and Kendall are all `None` (undefined zero variance), whereas `RPS` (`0.0125 [0.0, 0.0600]` vs `T05`; `0.0 [0.0, 0.0]` vs `T08`) and `TVD` (`0.0625`; `0.0`) remain sharp and finite.
4. **Why naive pooling creates Simpson's paradox — keep the cohorts stratified:** The `25` old tasks and `25` new tasks have `0/25` exact task-ID overlap (`12` token-overlap pairs across `5` new tasks; broad heuristic topics include sorting, sum/median, and prime/search) and a `+0.3890` regime shift in human mean (`0.5253` vs `0.9143`). Simply concatenating `75` old + `100` new artifacts and outputting each cohort's constant marginal (zero within-cohort skill!) yields a pooled `Pearson = 0.6557 [0.5046, 0.7850]`, `Spearman = 0.6594 [0.4894, 0.7915]`, and `Kendall = 0.5752 [0.4309, 0.6925]`. Therefore, reviewers should be shown **stratified two-regime 5-metric evaluation**: (i) **Old `25` (`75` files)** tests mid-quality discrimination (`mean = 0.5253`), and (ii) **New `25` (`100` files, evaluation-only, `0` placeholder references)** tests frontier near-ceiling calibration (`mean = 0.9143`) and bias sensitivity under `RPS`, `CE`, and `TVD` against the empirical human agreement reference (`LORO RPS = 0.0620`).

### Question 1B (`brando90/cert-judge`): Can incoming VeriBench human ratings make `cert-judge` more trustworthy and expand its evaluation to distributional metrics?

**They provide a prospective evaluation cohort; current evidence combines Experiment 39 re-scoring with the saved Experiment 51 historical reference:**

1. **Incoming multi-rater data offers a separate cohort for checking historical provenance and single-annotator limitations:** By `cert-judge` Experiment 41 (`provenance_by_task.csv`), `17/25` historical tasks had mismatched gold references (`1/25` missing, `5/25` placeholder tasks), and `74/75` candidates came from single-call `claude-3-7-sonnet-20250219`. Moreover, in `cert-judge` Experiment 51 (`n = 8` judges per family over `72` items), tuning/checking self-consistency `TI` against single-annotator 2-pass scalar Spearman (`H_paper_2passes`) gave apparently strong correlations (`Codex rho = 0.8333 p-val = 0.0154`, `Claude Opus rho = 0.6429 p-val = 0.0962`, `Qwen3-Coder rho = 0.9048 p-val = 0.0046`), **yet flipped negative under proper losses on that same target (`-mean RPS`: `-0.5714`, `-0.5000`, `-0.0714`) and under multi-rater 5-participant VeriBench labels** (`judge Spearman`: `-0.0952` Codex, `-0.4286` Opus, `-0.1905` Qwen3-Coder). Experiment 09 provides `0` placeholder references, `>0` theorem/lemma declarations on all `25` gold files, `4` modern native agents, and numeric responses from `>=2` distinct human raters per file so far (`247` ratings) for prospective held-out evaluation, after eligibility review.
2. **In Experiment 39 (`54` LLM judge configurations with `C_ms_gold` available), `C_ms_gold` is associated with proper scoring-rule performance:** After Gate G0 reproduction within `1e-12` (`opus55x|H2` saved vs recomputed Spearman difference `1.1e-16` (within `1e-12`); `C_ms_gold` test Spearman `0.5578 [0.0944, 0.7615]`, `p-val = 0.0126` one-sided permutation across `10,000` draws), `C_ms_gold` has positive observed correlations with `-RPS` (`r_s = 0.6078 [0.1282, 0.8659] p-val = 0.0077`, Kendall `0.4268 p-val = 0.0124`, Pearson `0.6867 p-val = 0.0050`), `-CE (Laplace alpha=0.5)` (`r_s = 0.5489`, Pearson `0.6960 p-val = 0.0022`), `-CE (eps=1e-6)` (`r_s = 0.5298`), `-TVD` (`r_s = 0.5758`, Pearson `0.6864 p-val = 0.0029`), and `-MAE` (`r_s = 0.6652 p-val = 0.0031`) on held-out `test` (`n = 16`), and reaches `r_s = 0.7633` (`-RPS`) and `0.7824` (`-CE Laplace alpha=0.5`, both `p-val = 9.999e-05`) across `all_llm` (`n = 54`). By contrast, `TI_var_trainnorm` fails across all held-out test criteria (`r_s = -0.3361` to `-0.2223`), and `PTI_v0_frozen` suffers fail-closed zero collapse (`1/15` non-zero in train, `0/18` in validation, `1/9` in test among defined values; respectively `3/18`, `2/20`, and `9/18` configurations lack the proxy), which must be reported alongside `C_ms_gold`.
3. **Important caveat when validating `cert-judge` on Experiment 09:** Because `91.50%` of live Experiment 09 ratings are `4` or `5`, scalar Spearman between judges on Experiment 09 alone will encounter range restriction and heavy ties; `cert-judge` should validate `C_ms_gold` and judge-selection proxies on **both** Experiment 09 proper losses (`RPS`, `CE`, `TVD` against empirical human PMFs) **and** historical Old 25 (kept unpooled).

---

## 2. Provenance & cohort comparison (`0/25` overlap, recorded Experiment 09 reference checks)

All provenance checks come directly from [summary_old_vs_new_11-24-2026.json](results/summary_old_vs_new_11-24-2026.json) (`section1_disjointness_and_provenance`):

```
+----------------------------+-------------------------------+-----------------------------------+
| Property                   | Old 25 (Exp 01 / dataset.json)| New 25 (Exp 09 live 11-24-2026)   |
+----------------------------+-------------------------------+-----------------------------------+
| Tasks / Artifacts          | 25 tasks / 75 artifacts       | 25 tasks / 100 artifacts          |
| Agents per task            | 3 stochastic samples          | 4 frontier native agents          |
| Solver model(s)            | 74/75 claude-3-7-sonnet-      | Codex GPT-6 Astra, Claude Code    |
|                            | 20250219 (temp 0.7, single    | Fable 5.1, Grok CLI 4.7,          |
|                            | call, no compiler loop);      | Antigravity CLI Gemini 4 Argon    |
|                            | 1 missing receipt             | (cohort SHA-256 fe5ecb9f...)       |
| Exact task-ID overlap      | 0 / 25 exact matches (12 heuristic token-overlap pairs)|
| Reference problems         | Exp 100: 9 ref drift, 5       | 0 placeholder tasks; all 25 gold  |
|                            | placeholder; Exp 41: 17       | files contain >0 theorem/lemma    |
|                            | mismatched, 7 matched, 1 miss | declarations                      |
| Artifact-equal human mean  | 0.5253 (195 expert ratings)   | 0.9143 (247 numeric ratings >=2/f)|
+----------------------------+-------------------------------+-----------------------------------+
```

Token overlap is only a heuristic and does not establish task-family independence. The 12 matched pairs involve five new tasks: `task_01_heap_sort` and `task_06_counting_sort` share `"sort"` with `bubble_sort`, `insertion_sort`, `merge_sort`, `selection_sort`; `task_09_sum_of_digits` shares `"sum"` with `humaneval_8_sum_product`; `task_10_lower_median` shares `"median"` with `humaneval_47_median`; `task_15_prime_fibonacci_search` shares `"search"` / `"prime"` with `binary_search` / `humaneval_31_is_prime`.

---

## 3. Live Experiment 09 human ratings (`247` ratings) & empirical inter-rater agreement (`11-24-2026`)

Synced via public Google Sheets CSV export across `33` verified live Sheets (`A1` + `32` team/Vals in `RAW_MANIFEST.json`; plus `T30` Max Sieb as a 34th Sheet outside `RAW_MANIFEST.json` that returned HTTP `401` and remains explicitly unverified with `0` local observations).

### 3.1 Active raters, score distributions, confidence, timing, and attestations

Across all `100` files: `55` files have `2` raters, `43` files have `3` raters, and `2` files have `4` raters (`247` numeric ratings, `0` `N/A` rows). Overall histogram on `0..5`: `{0: 0, 1: 7, 2: 1, 3: 13, 4: 46, 5: 180}`, raw rating mean `4.5830` (`0.9166` on `[0, 1]`), share `>= 4`: `91.50%` (`226 / 247`). Attestations across the `247` scored rows: `116` `"yes"` (`T05=100, T06=15, V04=1`), `100` `"partial"` (`T08=100`, non-dropdown free text), `31` blank (`T12=30, T06=1`).

```
+-------+----------------------+-----+--------+-------+-----------+----------------+-----------------+
| Rater | Name                 |   n | Mean   | SD    | >=4 Share | Attestation    | Median time     |
|       |                      |     | (0..1) | (0..5)|           | (scored rows)  | (n entries)     |
+-------+----------------------+-----+--------+-------+-----------+----------------+-----------------+
| T05   | Srivatsava Daruru    | 100 | 0.8760 | 0.8965|    87.0%  | 100 yes        | 4.0 min (100)   |
| T08   | Amy Lu               | 100 | 0.9480 | 0.7736|    95.0%  | 100 partial    | None (0)        |
| T12   | Rakshit Kaushik      |  30 | 0.9000 | 0.9738|    90.0%  | 30 blank       | None (0)        |
| T06   | Donald Poindexter Jr |  16 | 1.0000 | 0.0000|   100.0%  | 15 yes, 1 blank| None (0)        |
| V04   | Vaibhav Mahajan      |   1 | 1.0000 | 0.0000|   100.0%  | 1 yes          | 15.0 min (1)    |
+-------+----------------------+-----+--------+-------+-----------+----------------+-----------------+
```

**Response anomalies preserved in the raw CSVs:**
- `T05` (`Srivatsava Daruru`) and `T25` (`John Sarracino`, `0` scores) reordered rows in their Google Sheets; canonical CSV preservation holds and Experiment 26 joins strictly by `item_id` against `Brando_Miranda__native_main_A1.csv`.
- `T06` (`Donald Poindexter Jr`) typed `"this one has borderline spam."` in the `candidate_file` column on `native-heavy-11-11-2026__item020`; preserved verbatim in raw CSV and mapped cleanly by `item_id` to `task_16_certificate_hostname/agent_lean/agent_2.lean`.
- Experiment 15 costed timing combines `T05` (`100`) and `V04` (`1`) = `101` main entries (`median = 4.0` min, `mean = 4.0297` min, range `[3.0, 15.0]` min).

### 3.2 Pairwise human agreement & Leave-One-Rater-Out (`LORO`) human agreement reference (`10,000` task-cluster bootstrap draws)

```
+-------------------+-----+-------+-------+---------+---------+----------+----------+--------+---------+
| Rater pair        |  n  | Tasks | Exact | Within1 | Quad. K | RPS      | Pearson  | Spearm | Bias    |
| (Pred vs Target)  |     |       | match |         |         | [95% CI] | [95% CI] | [95%]  | (means) |
+-------------------+-----+-------+-------+---------+---------+----------+----------+--------+---------+
| T08 vs T05        | 100 |   25  | 0.620 |   1.000 |  0.7496 | 0.0760   | 0.8285   | 0.6243 | +0.0720 |
|                   |     |       |       |         |         | [.046,   | [.690,   | [.404, | (.9480  |
|                   |     |       |       |         |         |  .108]   |  .888]   |  .775] |  .8760) |
| T12 vs T05        |  30 |   20  | 0.700 |   1.000 |  0.8615 | 0.0600   | 0.9051   | 0.7805 | +0.0600 |
|                   |     |       |       |         |         | [.027,   | [.735,   | [.605, | (.9000  |
|                   |     |       |       |         |         |  .094]   |  .958]   |  .934] |  .8400) |
| T12 vs T08        |  30 |   20  | 0.767 |   1.000 |  0.8814 | 0.0467   | 0.8876   | 0.6653 | -0.0200 |
|                   |     |       |       |         |         | [.014,   | [.411,   | [.345, | (.9000  |
|                   |     |       |       |         |         |  .085]   |  .970]   |  .924] |  .9200) |
| T06 vs T05        |  16 |    5  | 0.938 |   1.000 |  0.0000 | 0.0125   | None     | None   | +0.0125 |
|                   |     |       |       |         |         | [.000,   | (all 5s) | (all 5)| (1.000  |
|                   |     |       |       |         |         |  .060]   |          |        |  .9875) |
| T06 vs T08        |  16 |    5  | 1.000 |   1.000 |    None | 0.0000   | None     | None   |  0.0000 |
|                   |     |       |       |         |         | [.000,   | (all 5s) | (all 5)| (1.000  |
|                   |     |       |       |         |         |  .000]   |          |        |  1.000) |
+-------------------+-----+-------+-------+---------+---------+----------+----------+--------+---------+
```

Additional `T08 vs T05` human agreement reference metrics (`100` files, `25` tasks): Kendall tau-b `0.5995 [0.3958, 0.7342]`, `CE (Laplace alpha=0.5)` `1.3983 [1.2335, 1.5741]`, `CE (eps=1e-6)` `5.2499 [3.1776, 7.4604]`, `TVD` `0.3800 [0.2300, 0.5400]`, `ICC(A,1)` `0.7515 [0.5286, 0.8412]`, `ICC(C,1)` `0.8196 [0.6236, 0.8866]`, `MAE (0-1)` `0.0760 [0.0460, 0.1080]`, Cohen's linear kappa `0.4826`. `T12 vs T05` Kendall tau-b `0.7533 [0.5916, 0.9080]`; `T12 vs T08` Kendall tau-b `0.6493 [0.3404, 0.9089]`. Across all `100` items under `LORO` (`artifact-weighted`), human agreement reference `RPS = 0.0620`, `CE (Laplace alpha=0.5) = 1.2413`, `TVD = 0.3367`, and empirical within-item human disagreement term = `0.0186` (unbiased finite-sample noise term `s^2/m = 0.0151`).

---

## 4. Zero-cost baselines on Experiment 09 (`100` files, `25` tasks, `$0.00` spend)

Evaluating zero-cost baselines without reading `sealed/` shows both why out-of-distribution constant baselines fail under regime shift and why correlation fails on frontier agents:

```
+-----------------------------------+-------------+------------+-------------+--------------+-------------+
| Model / Baseline (n = 100, 25 t.) | RPS         | CE (Lap    | TVD         | Spearman     | Signed Bias |
|                                   | [95% CI]    | alpha=0.5) | [95% CI]    | [95% CI]     | (pred, hum) |
+-----------------------------------+-------------+------------+-------------+--------------+-------------+
| Old-25 train constant PMF         | 0.2239      | 1.7834     | 0.7477      | None         | -0.3510     |
|                                   | [.206,.241] | [1.74,1.83]| [.705,.788] |              | (.563,.914) |
| Theorem-count ratio (all decl.)   | 0.0819      | 1.3011     | 0.2883      | 0.3105       | +0.0606     |
|                                   | [.045,.122] | [1.17,1.43]| [.175,.405] | [.032,.517]  | (.975,.914) |
| Theorem-count ratio (public only) | 0.0898      | 1.3018     | 0.2900      | 0.2516       | +0.0658     |
|                                   | [.049,.135] | [1.17,1.44]| [.172,.414] | [-.022,.442] | (.980,.914) |
| In-sample oracle constant (ref)   | 0.0677      | 0.8462     | 0.3593      | None         |  0.0000     |
|                                   | [.043,.095] | [0.63,1.08]| [.311,.415] |              | (.914,.914) |
| LORO human agreement (reference)  | 0.0620      | 1.2413     | 0.3367      | --           | --          |
+-----------------------------------+-------------+------------+-------------+--------------+-------------+
```

- **Paired contrasts for `theorem_count_ratio_all_declarations` (`10,000` task-cluster bootstrap draws):**
  - Versus `Old-25 train constant`: `diff_rps = -0.1419 [-0.1937, -0.0873]` (`p-val = 9.999e-05` paired two-sided task-cluster bootstrap), `diff_ce_laplace05 = -0.4823 [-0.6486, -0.3105]` (`p-val = 9.999e-05`), `diff_tvd = -0.4594 [-0.6094, -0.3071]` (`p-val = 9.999e-05`), `diff_mae = -0.2869 [-0.3515, -0.2174]` (`p-val = 9.999e-05`). Note `CE (eps=1e-6) = 3.8937 [2.3205, 5.5312]` is higher than the smoothed constant (`diff = +2.1093`, `p-val = 0.0076`) because linearly interpolated point predictions place `1e-6` mass on extreme mispredictions when a syntactically full-count file omits semantic pre/postconditions.
  - Versus `In-sample oracle constant`: `diff_rps = +0.0142 [-0.0007, +0.0308]` (`p-val = 0.0638`), `diff_ce_laplace05 = +0.4549 [+0.3366, +0.5586]` (`p-val = 9.999e-05`; the `RPS` difference remains inconclusive), `diff_tvd = -0.0709 [-0.1516, +0.0115]` (`p-val = 0.0936`). Even knowing `mean_ratio = 0.9749` (`90.0%` have `ratio == 1.0`) gives `Pearson = 0.2562 [-0.0196, 0.5421]`, `Spearman = 0.3105 [0.0316, 0.5170]`, `Kendall = 0.2790 [0.0296, 0.4691]`, `ICC(A,1) = 0.1892 [-0.0109, 0.4664]` — a warning that syntactic theorem counts do not establish semantic coverage. These aggregate metrics do not identify the causes of individual low ratings, and correlation does not measure probability calibration.

---

## 5. Anatomy of `"0.6, 0.8, 0.8"`, CI width scaling (`k=10` vs `k=25`), and Simpson's paradox

### 5.1 Old 25 Experiment 22 split breakdown (exact values from Experiment 22 `aggregates_5metrics.json`)

```
+---------------+-------+-----+----------+----------+----------+-------------+-------------+-------------+
| Split         | Files | Tsk | Spearman | Pearson  | Kendall  | RPS [95%CI] | Const RPS   | Bias (Share)|
|               |       |     | [95% CI] | [95% CI] | tau-b    |             | [95% CI]    | MSE_bias%   |
+---------------+-------+-----+----------+----------+----------+-------------+-------------+-------------+
| train         |    30 |  10 | 0.6400   | 0.6576   |   0.5445 | 0.1793      | 0.1736      | +0.0733     |
|               |       |     | [.24,.91]| [.16,.92]|          | [.118,.255] | [.134,.218] | (8.15%)     |
| val           |    15 |   5 | 0.8800   | 0.8601   |   0.8231 | 0.1285      | 0.1668      | +0.0978     |
|               |       |     | [.70,1.0]| [.77,1.0]|          | [.056,.207] | [.108,.226] | (28.30%)    |
| test          |    30 |  10 | 0.8257   | 0.8578   |   0.6982 | 0.1954      | 0.1836      | +0.1811     |
|               |       |     | [.32,.97]| [.71,.94]|          | [.125,.267] | [.142,.228] | (55.04%)    |
| test_ordinary |    24 |   8 | 0.6519   | 0.8347   |   0.5133 | 0.2234      | 0.1783      | +0.2056     |
|               |       |     | [-.17,.92]| [.45,.96]|          | [.141,.297] | [.127,.234] | (58.35%)    |
| all_75        |    75 |  25 | 0.7578   | 0.7657   |   0.6466 | 0.1756      | 0.1762      | +0.1213     |
|               |       |     | [.55,.90]| [.57,.89]|          | [.133,.221] | [.151,.204] | (25.83%)    |
+---------------+-------+-----+----------+----------+----------+-------------+-------------+-------------+
```

Judge vs human means across Old 25 splits (`member_median`): `train` `0.6367` vs `0.5633`; `val` `0.6533` vs `0.5556`; `test` `0.6533` vs `0.4722`; `test_ordinary` `0.5667` vs `0.3611`; `all_75` `0.6467` vs `0.5253`.

### 5.2 Task-count CI scaling (`k = 10` vs `k = 25` resampled tasks, `10,000` draws) and Simpson's paradox pooling test

- **CI half-width shrinkage (`k = 25` / `k = 10`):**
  - `T08` vs `T05`: `RPS` half-width `0.0475 -> 0.0310` (`0.6526x`), `TVD` `0.2375 -> 0.1550` (`0.6526x`), `CE (Laplace alpha=0.5)` `0.2609 -> 0.1703` (`0.6526x`), `Pearson` `0.2066 -> 0.0994` (`0.4809x`), `Spearman` `0.2741 -> 0.1859` (`0.6783x`), `Kendall` `0.2539 -> 0.1692` (`0.6664x`), `signed_bias` `0.0500 -> 0.0310` (`0.6200x`).
  - `Theorem-count ratio`: `RPS` half-width `0.0604 -> 0.0384` (`0.6359x`), `Spearman` `0.3819 -> 0.2427` (`0.6356x`), `Kendall` `0.3508 -> 0.2198` (`0.6265x`), `Pearson` `0.3884 -> 0.2809` (`0.7232x`).
- **Simpson's paradox demonstration (`175` pooled artifacts across `50` tasks; no within-cohort discrimination):**
  - Assigning `Old 25` its own cohort mean PMF (`mean = 0.5253`) and `New 25` its own cohort mean PMF (`mean = 0.9143`) has undefined correlation within either cohort because its predictions are constant, yet pooling across the two regimes produces `Pearson = 0.6557 [0.5046, 0.7850]`, `Spearman = 0.6594 [0.4894, 0.7915]`, `Kendall = 0.5752 [0.4309, 0.6925]`, `ICC(A,1) = 0.6027 [0.4685, 0.7080]`, and `RPS = 0.1131 [0.0905, 0.1377]` (`paired diff vs global constant = -0.0464 [-0.0718, -0.0206]`, `p-val = 0.0002`). **Never pool Old and New regimes to claim higher judge correlation.**

---

## 6. Bridge to `brando90/cert-judge`: Experiment 39 and Experiment 51 under 5-metric distributional evaluation

Re-scoring Experiment 39 harvests against the `45` available held-out items (`val + test` of Old `25`) retains `60` configurations, including `56` LLM configurations and `4` controls: `50` cover `45/45` items, `9` cover `42/45`, and `1` covers `44/45`. Metrics use each configuration's observed items; unequal item coverage is a comparison limitation. Actual repeat counts are preserved per artifact in `laplace_smooth_counts`. Confidence intervals resample judge configurations, holding the shared rated artifacts fixed; they do not include uncertainty over new task or judge families. The multiple correlation tests are exploratory and their p-values are unadjusted. Re-scoring matches Gate G0 within `1e-12` (`opus55x|H2` diff `1.1e-16`, `C_ms_gold` test Spearman `0.5578`, `n = 16`) and tests whether label-free proxies track distributional evaluation criteria (`10,000` bootstrap and permutation draws):

```
+------------------+---------------+-------------------------+------------------------+------------------------+
| Split & Proxy    | Target        | Spearman [95% CI]       | Kendall [95% CI]       | Pearson [95% CI]       |
| (n configs)      | criterion     | (one-sided perm p-val)  | (one-sided perm p-val) | (one-sided perm p-val) |
+------------------+---------------+-------------------------+------------------------+------------------------+
| test C_ms_gold   | saved_spearman| 0.5578 [0.094, 0.762]   | 0.3598 [0.055, 0.593]  | 0.6429 [0.449, 0.919]  |
| (n = 16)         |               | p-val = 0.0126          | p-val = 0.0288         | p-val = 0.0096         |
| test C_ms_gold   | -RPS          | 0.6078 [0.128, 0.866]   | 0.4268 [0.045, 0.730]  | 0.6867 [0.485, 0.896]  |
| (n = 16)         |               | p-val = 0.0077          | p-val = 0.0124         | p-val = 0.0050         |
| test C_ms_gold   | -CE (Lap .5)  | 0.5489 [0.040, 0.847]   | 0.3766 [-.018, 0.696]  | 0.6960 [0.426, 0.906]  |
| (n = 16)         |               | p-val = 0.0155          | p-val = 0.0244         | p-val = 0.0022         |
| test C_ms_gold   | -TVD          | 0.5758 [0.063, 0.879]   | 0.4034 [0.000, 0.741]  | 0.6864 [0.431, 0.892]  |
| (n = 16)         |               | p-val = 0.0113          | p-val = 0.0168         | p-val = 0.0029         |
| test C_ms_gold   | -MAE          | 0.6652 [0.220, 0.897]   | 0.4937 [0.143, 0.784]  | 0.7538 [0.613, 0.930]  |
| (n = 16)         |               | p-val = 0.0031          | p-val = 0.0044         | p-val = 0.0017         |
| test TI_var      | -RPS          | -0.2782 [-.733, 0.229]  | -0.2244 [-.570, 0.133] | -0.2446 [-.686, 0.224] |
| (n = 18)         |               | p-val = 0.8675          | p-val = 0.9062         | p-val = 0.8310         |
| all_llm C_ms_gold| -RPS          | 0.7633 [0.632, 0.843]   | 0.5512 [0.434, 0.659]  | 0.7445 [0.635, 0.843]  |
| (n = 54)         |               | p-val = 9.999e-05       | p-val = 9.999e-05      | p-val = 9.999e-05      |
| all_llm C_ms_gold| -CE (Lap .5)  | 0.7824 [0.656, 0.859]   | 0.5699 [0.456, 0.671]  | 0.7423 [0.631, 0.841]  |
| (n = 54)         |               | p-val = 9.999e-05       | p-val = 9.999e-05      | p-val = 9.999e-05      |
| all_llm C_ms_gold| -TVD          | 0.7680 [0.643, 0.843]   | 0.5547 [0.440, 0.660]  | 0.7335 [0.625, 0.832]  |
| (n = 54)         |               | p-val = 9.999e-05       | p-val = 9.999e-05      | p-val = 9.999e-05      |
+------------------+---------------+-------------------------+------------------------+------------------------+
```

Additional verified Experiment 39 / Experiment 51 observations:
- `test` `C_ms_gold` against `-CE (eps=1e-6)`: Spearman `0.5298 [0.0226, 0.8471]` (`p-val = 0.0191`), Kendall `0.3933 [-0.0175, 0.7143]` (`p-val = 0.0203`), Pearson `0.6422 [0.3698, 0.8536]` (`p-val = 0.0060`).
- `val_llm` (`n = 20`) `C_ms_gold`: `saved_spearman` `r_s = 0.7624 [0.5140, 0.8877]`, `-RPS` `0.7394 [0.4776, 0.8668]` (`p-val = 0.0004`), `-CE (Laplace alpha=0.5)` `0.7564 [0.4798, 0.8891]` (`p-val = 9.999e-05`), `-TVD` `0.7386 [0.4796, 0.8589]` (`p-val = 0.0002`).
- `PTI_v0_frozen` is degenerate on Experiment 39 (`1/15` non-zero in train, `0/18` in validation, `1/9` in test among defined values; respectively `3/18`, `2/20`, and `9/18` configurations lack the proxy), producing `p-val = 0.0666` (`n = 15` train), undefined on `val_llm`, and `r_s = -0.2739` (`p-val = 0.7760`, `n = 9`) on `test`.
- Experiment 51 (`n = 8` per family) underscores why Experiment 09's multi-rater evaluation with reference checks is vital: when validated on `H_vb_5participants(all 5 rated)`, proper distributional alignment was negative (`Codex -RPS rho = -0.5714 p-val = 0.1511`; `Opus -RPS rho = -0.5238 p-val = 0.1966`; `Qwen3-Coder -RPS rho = -0.6667 p-val = 0.0831` and `-CE (Laplace alpha=0.5) rho = -0.7619 p-val = 0.0368`), illustrating that conclusions differ between scalar single-annotator `H_paper_2passes` Spearman and these other targets on small `n = 8` sweeps.

---

## 7. Ready-to-run next steps once frozen judges are scored on Experiment 09 (`$0` planning check; requires explicit user approval before paid inference)

1. **Score already-selected frozen judges once on the `100` Experiment 09 artifacts** (holding Experiment 09 **strictly sealed for evaluation only** — no prompt edits, no threshold retuning, no mixture weight fitting): Method 2 Pearson-selected, Method 4 `CE`-selected, Method 4 `RPS`-selected, `opus55x|H2` / `H1`, and `gpt-6-astra` / `gemini-4-argon` (frontier models only, after explicit budget confirmation; note `ub9sc`'s pre-registered `25_do_more_human_ratings_improve_judge_evaluation_old_new_pooled_start_24Nov2026` landed on `main` at `3f5a460` and is already running frozen `H2` prompt calls with `GPT-6 Astra` and `Claude Opus 5.5` on the new cohort).
2. **Run Experiment 22's deterministic 5-metric evaluator against the live Experiment 09 CSVs:**

```bash
python3 experiments/22_evaluate_veribench_judges_on_75_outputs_distribution_losses_vs_correlations_start_16Nov2026/scripts/evaluate_5metrics.py score-forecasts \
  --ratings-csv experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/ratings/*__native_main_*.csv \
  --forecasts-json <path_to_frozen_judge_forecasts_on_exp09.json> \
  --bootstrap 10000 \
  --seed 20261124 \
  --out <path_to_exp09_5metric_eval.json>
```

3. **Descriptive comparison references on Experiment 09 (not prespecified acceptance gates):** Beat the `Old-25 train constant` (`RPS = 0.2239 [0.2057, 0.2405]`), beat or compete with `theorem_count_ratio` (`RPS = 0.0819 [0.0451, 0.1219]`) and `in_sample_constant` (`0.0677 [0.0431, 0.0951]`), and compare against the `LORO` human agreement reference (`RPS = 0.0620`, `T08 vs T05` `0.0760 [0.0460, 0.1080]`), reporting Method 2 versus Method 4 differences jointly with Old 25 stratified results.
4. **In `brando90/cert-judge`:** Run `C_ms_gold` and `PTI` probes on the `100` Experiment 09 files once frontier-judge repeats exist, evaluating meta-proxy validity directly against `-RPS`, `-CE (Laplace alpha=0.5)`, and `-TVD` alongside Old 25 stratified validation.
5. **Follow up on unverified `T30` (Max Sieb HTTP 401), `T08` (`partial` free-text attestation), `T12` (`30` blank attestations), `T06` (`item020` cell edit + `16/16` score-`5` check)** before locking the final Experiment 09 collection freeze.

**TLDR-end:** [trustworthy-theorem-judges: experiments/26_how_new_and_old_human_ratings_fix_06_08_08_and_expand_5metric_eval_start_24Nov2026] Documents level bias (`55.04%` of test `MSE`), uncertainty with small task counts (`k = 5..10`), and recorded reference problems without establishing their causal effects on `"0.6, 0.8, 0.8"`; `247` live Experiment 09 ratings support a future stratified evaluation alongside Old 25 under `RPS`, `CE`, and `TVD`; they do not yet validate the frozen judges on the new cohort.
