# How and why we evaluate theorem judges with all 5 metrics (`RPS`, `CE`, `TVD`, `Pearson`, `Spearman`)

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/22_evaluate_veribench_judges_on_75_outputs_distribution_losses_vs_correlations_start_16Nov2026/EVAL_DOCUMENT_5_METRICS_11-16-2026.md>

**TLDR:** Relying on `Pearson` and `Spearman` correlations alone hid a `+0.181` (`+0.91` points on `0–5`) leniency bias and failed to catch that the previously selected VeriBench judge performed worse than a constant baseline on held-out test Ranked Probability Score (`RPS = 0.1954` vs `0.1836`). Going forward, every large language model (LLM) judge evaluation for formal specification coverage (FSC) in `trustworthy-theorem-judges` uses **normalized `RPS` as the primary metric**, **`Cross-Entropy` (`CE`) and `Total Variation Distance` (`TVD`) as secondary distribution metrics**, and **`Pearson` and `Spearman` (with `Kendall tau-b`, mean absolute error [`MAE`], and `signed bias`) as scalar association diagnostics**, reporting all 5 side-by-side (`no DT` [no differential testing], central processing unit [CPU]-only over cached human-rating judgments).

**Methodology sources:** [Correlation vs loss for training LLM judges brief (`11-13-2026`)](https://claude.ai/artifact/Rg2hYLxYMGJAte7jcV7kKV) · [sister repository `judges-dont-need-psychometrics-or-corr`](https://github.com/brando90/judges-dont-need-psychometrics-or-corr) · [experiments/02_design_a_judge_that_predicts_human_ratings_0_to_5_start_06Nov2026 (`PRIORITY_2_VS_4_11-09-2026.md`)](../02_design_a_judge_that_predicts_human_ratings_0_to_5_start_06Nov2026/PRIORITY_2_VS_4_11-09-2026.md) · [recomputed VeriBench 5-metric results (`results.md`)](results.md).

---

## 1. The problem: why `"0.6, 0.8, 0.8"` misled us

In `experiments/archive/01_veribench_25_tasks_3_samples_5_raters_judge_evaluation_start_03May2026_end_29Sep2026` (VeriBench experiment 100), the selected two-model judge (`openai/gpt-6-sol-high` + `anthropic/claude-opus-5-5-no-fallback` with the `H2` human-mirror + 4-convention + 4-demo prompt, 3 calls per member) gave the familiar `"0.6, 0.8, 0.8"` agreement profile across the `10 / 5 / 10` (`train / validation / test`) task splits:

- **Train** (`30` outputs, `10` tasks, `78` expert ratings): `Spearman = 0.6400`, `Pearson = 0.6576`.
- **Validation** (`15` outputs, `5` tasks, `39` expert ratings): `Spearman = 0.8800`, `Pearson = 0.8601`.
- **Test** (`30` outputs, `10` tasks, `78` expert ratings): `Spearman = 0.8257`, `Pearson = 0.8578`.

Under correlations alone, two things looked confusing: (1) validation and test looked strangely *higher* than train (`0.64 -> 0.88 -> 0.83`), and (2) `0.83–0.86` looked close to `"trustworthy"`.

When we re-evaluate the exact same frozen 6-call judge (`experiments/22_evaluate_veribench_judges_on_75_outputs_distribution_losses_vs_correlations_start_16Nov2026`) on the 5-metric panel alongside the out-of-sample `constant` training-marginal baseline, the picture flips:

- On **test `RPS`** (range `[0, 1]`, lower is better), the selected judge scores **`0.1954 [0.1246, 0.2669]`**, which is **worse than predicting the training-set marginal rating histogram for every test output (`0.1836`, paired difference `+0.0118 [-0.0898, +0.1085]`, `p-val=0.8244`)**.
- On the **24 ordinary-reference test outputs** (`8` tasks, `66` ratings, removing 2 tasks whose references were placeholders when rated), its `RPS` degrades further to **`0.2234 [0.1405, 0.2965]`** vs constant **`0.1783`** (`+0.0451 [-0.0771, +0.1511]`, `p-val=0.457`), and `Spearman` drops to `0.6519 [-0.1662, +0.9161]`.
- Why did `Pearson` stay at `0.8578` (`0.8347` on ordinary items) while `RPS` degraded from validation (`0.1285`) to test (`0.1954`)? Because **the judge's positive leniency bias more than doubled** from train (`+0.0733`) and validation (`+0.0978`) to test (`+0.1811`, `judge mean 0.6533` vs `human mean 0.4722` — nearly `+1` full rating point on the `0–5` scale!), accounting for **`55.0%`** of its test mean squared error (`58.4%` on ordinary test items), and `Pearson` ignores additive shifts and scale mismatches completely.

---

## 2. Exact definitions of all 5 evaluation metrics (plus required diagnostics)

For candidate formalization artifact $i \in \{1,\dots,n\}$ (pairing Python source, candidate Lean file, and gold reference Lean file), let $r_{i,1},\dots,r_{i,m_i} \in \{0,1,2,3,4,5\}$ be the $m_i$ observed human ratings. Define:

- **Empirical human probability mass function (PMF):** $\hat{p}_i(r) = \frac{1}{m_i}\sum_{h=1}^{m_i} \mathbf{1}\{r_{i,h} = r\}$.
- **Empirical human cumulative distribution function (CDF):** $P_i(k) = \sum_{r=0}^k \hat{p}_i(r)$ for thresholds $k \in \{0,1,2,3,4\}$.
- **Judge forecast PMF and CDF:** $q_i = (q_i(0),\dots,q_i(5))$ with $q_i(r) \ge 0$, $\sum_{r=0}^5 q_i(r) = 1$, and $Q_i(k) = \sum_{r=0}^k q_i(r)$.
- **Normalized expected scores on $[0, 1]$:** judge expectation $\mu_i = \sum_{r=0}^5 \frac{r}{5} q_i(r)$ and human mean $\bar{h}_i = \sum_{r=0}^5 \frac{r}{5} \hat{p}_i(r)$.

**Equal-artifact weighting rule:** Every per-rating loss is averaged **within each artifact first** (`1 / m_i`), and then averaged **equally across artifacts** (`1 / n`). Giving an artifact more raters never silently increases its weight in the benchmark score.

| Role | Metric | Formula (per artifact $i$, then mean over $i=1..n$) | Range & direction | What it captures |
| --- | --- | --- | --- | --- |
| **Primary** | **Normalized Ranked Probability Score (`RPS`)** | $\frac{1}{m_i}\sum_{h=1}^{m_i}\frac{1}{5}\sum_{k=0}^4 \big(Q_i(k) - \mathbf{1}\{r_{i,h} \le k\}\big)^2$ | `[0, 1]`, **lower is better** | Full ordinal rating distribution: penalizes distance in rating points, score bias, and mispredicted rater spread. |
| **Secondary** | **Cross-Entropy (`CE`)** | $\frac{1}{m_i}\sum_{h=1}^{m_i}\big(-\ln q_i(r_{i,h})\big) = -\sum_{r=0}^5 \hat{p}_i(r)\ln q_i(r)$ | `[0, +\infty)`, **lower is better** (nats) | Unordered log-likelihood of observed ratings; catches zero-mass/overconfident tail misses immediately. |
| **Secondary** | **Total Variation Distance (`TVD`)** | $\frac{1}{2}\sum_{r=0}^5 |q_i(r) - \hat{p}_i(r)|$ | `[0, 1]`, **lower is better** | Direct $L_1$ mass discrepancy between $q_i$ and the artifact's empirical human histogram $\hat{p}_i$. |
| **Diagnostic** | **Pearson correlation (`r`)** | $\frac{\sum_i (\mu_i - \bar{\mu})(\bar{h}_i - \bar{\bar{h}})}{\sqrt{\sum_i(\mu_i - \bar{\mu})^2 \sum_i(\bar{h}_i - \bar{\bar{h}})^2}}$ | `[-1, 1]`, **higher is better** | Linear tracking of normalized expected ratings across artifacts; blind to shift and positive scaling. |
| **Diagnostic** | **Spearman rank correlation (`rho`)** | Pearson correlation of average-tie ranks of $(\mu_1,\dots,\mu_n)$ and $(\bar{h}_1,\dots,\bar{h}_n)$ | `[-1, 1]`, **higher is better** | Monotonic ranking of artifacts by expected score; blind to any strictly increasing score distortion. |

**Required companion diagnostics (reported alongside the 5 metrics):**
- **`Kendall tau-b`** (pairwise ordering with ties),
- **Normalized Root Mean Squared Error (`nRMSE`)**, **Mean Absolute Error (`MAE`)**, and **signed mean bias** ($\frac{1}{n}\sum_i(\mu_i - \bar{h}_i)$, judge minus human, positive = lenient, with both means shown),
- **Intraclass correlation coefficients `ICC(A,1)`** (two-way single-score absolute agreement, penalizing offset) and **`ICC(C,1)`** (two-way single-score consistency, ignoring offset).

**Important smoothing rule for discrete-call judges:** Native six-probability judges should output valid probabilities directly without ad hoc floors. For historical or sampled-repeat judges (`K = 3` or `K = 6` integer calls per artifact), unsupported bins receive zero empirical mass, making raw `CE` infinite. Our standard floor for historical mixture comparisons (`experiments/21_...` and `experiments/22_...`) is `smooth(hist, eps=1e-6)`, **and we always report `eps=1e-3` and `Laplace(alpha=0.5)` sensitivity checks** because `CE` scales directly with `-ln(eps)` while `RPS` stays bounded and stable (`0.1954` at `1e-6` vs `0.1941` at `1e-3`).

---

## 3. Why `RPS`, `CE`, and `TVD` beat correlations for evaluating judge quality

From `<https://claude.ai/artifact/Rg2hYLxYMGJAte7jcV7kKV>` and `<https://github.com/brando90/judges-dont-need-psychometrics-or-corr>`, there are four concrete mathematical and empirical failures of correlation-only evaluation:

1. **Correlations are blind to distribution shape and human disagreement.**
   Any judge's expected rating equals the sum of its survival probabilities, $\mathbb{E}_{q}[R] = \sum_{k=0}^4 \Pr_q[R > k]$. Opposite errors across thresholds cancel out completely in the mean, while `RPS` squares each threshold gap before adding.
   - *Worked example from the brief:* Suppose raters split 50/50 between `3` and `5` on an artifact ($\hat{p} = (0,0,0,0.5,0,0.5)$). **Judge A** predicts `(0,0,0,0.5,0,0.5)`, capturing the true split; **Judge B** puts `1.0` on `4`. Both have expected rating `4.0` (`0.8` on `[0,1]`), so **`Pearson` and `Spearman` cannot distinguish them at all**, whereas **`RPS = 0.10` for Judge A vs `0.20` for Judge B** (and `TVD = 0.0` vs `1.0`).
   - *Controlled proof (`01_conditional_binomial_distribution_identification_start_08Nov2026`):* Across five candidate models sharing the exact `Bin(5, t)` conditional mean `5t` but differing in spread, `Pearson`, `Spearman`, `Kendall`, and scalar mean squared error (`MSE`) tie across all five candidates in **`256 / 256`** rating replications, whereas `CE`, six-category `Brier` score, and `RPS` select the true distribution in **`256 / 256`** replications with `2–3` ratings per item (`249/256`, `245/256`, `245/256` with just `1` rating).

2. **`Pearson` explicitly discards bias and scale mismatch.**
   Over any evaluation set, normalized scalar mean squared error decomposes exactly into three non-negative terms:
   $$\frac{1}{n}\sum_{i=1}^n (\mu_i - \bar{h}_i)^2 = \underbrace{(\bar{\mu} - \bar{\bar{h}})^2}_{\text{bias}^2} + \underbrace{(s_\mu - s_{\bar{h}})^2}_{\text{scale mismatch}^2} + \underbrace{2 s_\mu s_{\bar{h}}(1 - r_{\mu,\bar{h}})}_{\text{the only term Pearson sees}}.$$
   Any positive affine rescaling $\mu'_i = a \mu_i + b$ ($a > 0$) leaves `Pearson` (`r`) completely unchanged. For example, predicting $\mu = 0.1 + 0.08\bar{h}$ gives `r = 1.000` despite massive bias and variance collapse. On VeriBench's real test split (`n=30`), `55.0%` of the `"0.6, 0.8, 0.8"` judge's `MSE` (`0.0596`) comes from squared bias (`+0.1811` leniency), and on ordinary-reference test items (`n=24`), bias (`58.4%`) plus scale mismatch (`15.5%`) make up **`73.8%`** of `MSE` — completely invisible to `Pearson = 0.8347`!

3. **Real VeriBench ranking inversions between `Pearson`/`Spearman` and `RPS`.**
   On the canonical `10`-task VeriBench test split (`n=30`), evaluating single frontier judges (`3` calls each) by correlations gives the *opposite* quality signal from `RPS`:
   - `H2_argon` (`gemini-4-argon`) leads correlations at **`Pearson = 0.873`, `Spearman = 0.921`**, followed by `H2_opus` (`0.862`, `0.840`), `H2_astra` (`0.849`, `0.852`), and `H0_sol` last among `Sol`/`Opus` at **`0.664`, `0.591`**.
   - Yet on test **`RPS`**, **`H0_sol` (`0.1907`) beats every single `H2` judge (`0.1959`–`0.2078`)** because `H0_sol` is nearly unbiased (`+0.014`), whereas every `H2` judge has severe leniency bias (`+0.166` to `+0.183`)! And *every single* unmixed 3-call judge loses on test `RPS` to predicting the constant training marginal (`0.1836`).
   - Similarly, on the 8-judge pool without post-hoc shrinkage (`lambda = 0.0`), the `② Pearson-trained` mixture chases `H2_argon` (`0.846 H2_argon + 0.154 H0_sol`), achieving high test correlations (`r = 0.885`, `rho = 0.851`) while scoring **significantly worse test `RPS` (`0.1693`) than the `④ RPS-trained` mixture (`0.1443`, difference `+0.0250 [+0.0063, +0.0427]`, `p-val=0.0074`)**!

4. **Test correlation depends on the test set's variance, not just the judge.**
   If you add two easy placeholder-reference tasks (as happened in the `30`-item vs `24`-item ordinary VeriBench test split), `Spearman` jumps from `0.652` to `0.826` purely because task variance increased, whereas `RPS` evaluates each artifact's forecast directly on `[0, 1]` (`0.2234` vs `0.1954`) and reveals both splits fail to beat the constant baseline.

---

## 4. Why `RPS` is primary over `CE` and `TVD` — and why we still report all 5

| Metric | Strengths in judge evaluation | Failure mode if used alone | Role in our 5-metric panel |
| --- | --- | --- | --- |
| **`RPS`** | **Proper scoring rule for ordered `0–5` ratings**: near miss (`4 vs 5`: `0.20`) beats far miss (`4 vs 0`: `0.80`). Bounded in `[0, 1]`. Unbiased difference estimator even with `1–3` human ratings per artifact because cumulative indicators pool counts across thresholds. Exact decomposition $\mathbb{E}[\text{RPS}] = \text{CDF error}^2 + \text{human disagreement}$. | Assumes equal spacing between rating steps (`0–1` vs `4–5`) and is gentler on rare extreme surprises than `CE`. | **Primary evaluation & selection metric** (`common validation RPS`, primary test endpoint). |
| **`CE`** | **Strictly proper likelihood rule**: strongly penalizes confident misses and detects zero-support predictions immediately. Works cleanly with `1` rating per item without needing empirical histograms. | Unbounded (`+inf` on any zero-probability category); with `3`–`6` discrete judge repeats, artificial probability floors (`eps=1e-6` vs `1e-3`) dominate raw values (`8.3` vs `4.2` nats), making a dumb constant marginal look better than informative sparse histograms (`1.81` vs `6.91` nats). | **Secondary metric** (especially decisive for native probability heads and tail probability alignment; always report probability floor). |
| **`TVD`** | **Intuitive `[0, 1]` mass overlap**: half the $L_1$ error between predicted and empirical rating distributions. Bounded and symmetric. | **Not proper against finite-sample histograms** and ignores `0–5` ordering. With sparse `m=1..3` ratings, plug-in `TVD` rewards overconfident point masses over the true spread (`0.40` vs `0.48` on a `60/40` split with `m=1`, where even the true distribution suffers `0.48`!). Note: this is per-artifact empirical `TVD`, **not** `TVD-MI` (`TVD mutual information`). | **Secondary distribution diagnostic** (compares full PMF mass overlap on `[0, 1]`; never used alone for model selection). |
| **`Pearson`** | Familiar linear association `[−1, 1]` between expected judge score and human mean. | Blind to constant shift (`bias`), scale compression, and rater spread. | **Diagnostic** (always accompanied by `signed bias`, `MAE`, and `ICC(A,1)`). |
| **`Spearman`** | Monotonic rank ordering `[−1, 1]` across artifacts; answers "does higher judge score rank above lower?". | Blind to monotonic score distortion, scale, bias, and spread; sensitive to tied ranks and task-set spread. | **Diagnostic** (useful when only artifact ranking is needed; accompanied by `Kendall tau-b`). |

**Why report all 5 together ("for the science"):**
Reporting only one number hides how a judge fails. Showing **`RPS`**, **`CE`**, **`TVD`**, **`Pearson`**, and **`Spearman`** in the same table makes every tradeoff explicit: across `1,000` random `20 / 5` splits on the `8`-judge VeriBench pool (`experiments/21_add_3_frontier_judges_to_pool_pearson_vs_ce_80_20_start_16Nov2026`), `②` (correlation-trained) and `④` (CE-trained) tie on `RPS` (`+0.0051 [-0.0034, +0.0136]`), **`④` beats `②` on `CE` (`+0.739`) and `TVD` (`+0.0276`)**, and **`②` beats `④` on `Spearman` (`+0.079`) and `Pearson` (`+0.049`)**. Without all 5 metrics, each side could cherry-pick a winner; with all 5 (`RPS` primary), the scientific conclusion is unambiguous.

---

## 5. How to run the 5-metric evaluator on incoming `experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026` human ratings

Once Brando (`A1`), Sri (`T05`), and the team fill ratings in `experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/ratings/*.csv` and you pair a JavaScript Object Notation (JSON) map of judge six-probability forecasts (`{"item_id": [q0, q1, q2, q3, q4, q5], ...}`), run the exact 5-metric panel with `10,000`-draw task-cluster bootstrap confidence intervals (CIs) via:

```bash
python3 experiments/22_evaluate_veribench_judges_on_75_outputs_distribution_losses_vs_correlations_start_16Nov2026/scripts/evaluate_5metrics.py \
  score-forecasts \
  --ratings-csv experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/ratings/Brando_Miranda__native_main_A1.csv \
                experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/ratings/Srivatsava_Daruru_Sri__native_main_T05.csv \
  --forecasts-json /path/to/private/forecasts.json \
  --out /path/to/private/eval_5metrics.json
```

Keep raw individual ratings and private forecast files outside public Git if sealed or restricted by `experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026`'s split policy; commit only aggregate tables and `results/` summaries.

**TLDR-end:** [ttj: experiments/22_evaluate_veribench_judges_on_75_outputs_distribution_losses_vs_correlations_start_16Nov2026] Use normalized `RPS` as primary, `CE` and `TVD` as secondary distribution metrics, and `Pearson` and `Spearman` (plus `Kendall tau-b`, `MAE`, and `signed bias`) as diagnostics—reporting all 5 together because correlations alone missed a `+0.181` test bias and worse-than-constant `RPS` on VeriBench's historical judge.
