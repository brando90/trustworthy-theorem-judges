# Pre-registration: Multi-family distributional judge, open-weight logit readout/LoRA, and proper-loss vs correlation on updated human ratings (11-26-2026)

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/28_multi_family_distributional_judge_and_open_weight_lora_on_new_ratings_start_26Nov2026/PREREG.md>

**TLDR:** Pre-registered before any new judge inference or test evaluation on the 11-26-2026 live human ratings (195 old expert ratings + 250 live new ratings = 445 ratings across 175 artifacts and 50 disjoint tasks). Evaluates (i) uniform-harness multi-family `H4` zero-demo distributional judges across frontier families, (ii) `Qwen3-8B` single-pass next-token logit readout and end-to-end LoRA fine-tuning (`CE` vs `RPS` vs `Pearson`), and (iii) proper-loss `(M+K)` logit-pool calibration against the set-aware constant, Experiment 27's frozen `F8` judge, and raw `H2`, with nested grouped inner cross-validation and zero test leakage.

**Dated:** 11-26-2026 (Thu), written and committed before any new judge call (`H4` or `Qwen3-8B`) and before any test-split evaluation. Owner: Brando Miranda.

## 1. Data, Live Sync Status, and Locked Splits (By Task, Never By Artifact)
Dated, anonymised copies live in `data_11-26-2026/`. Rater names and rater IDs are removed; ratings are sorted within each artifact.

- **Old set (Experiment 100 / 21 / 27):** 25 tasks, 75 artifacts, 195 expert ratings.
- **New set (Experiment 09 live sync, 11-26-2026 15:47 PST):** 25 disjoint tasks, 100 artifacts, **250** numeric ratings across 6 active non-coordinator raters (`100, 100, 30, 16, 3, 1`; `T30` verified `0/100` via signed-in Chrome Sheet CSV export; `A1` coordinator has `0/100`). Every artifact has 2 to 4 ratings (52 have 2, 46 have 3, 2 have 4). Score counts: `{1: 7, 2: 1, 3: 15, 4: 42, 5: 185}` (74.0% are `5`s). Against Experiment 27's 11-24-2026 freeze (`247` ratings), 10 artifacts changed (3 in Exp 27 train, 1 in Exp 27 val, 6 in Exp 27 test).
- **Pooled:** 50 disjoint tasks, 175 artifacts, 445 ratings.
- **Two locked task-level splits (`data_11-26-2026/task_splits_11-26-2026.csv`):**
  1. `exp27_split`: identical 20 train / 10 val / 20 test task partition from Experiment 27 (`105` train+val artifacts -> `70` test artifacts) for exact apples-to-apples comparison against Experiment 27's frozen `F8` judge. **Prior-exposure disclosure:** the 10 old test tasks were seen by `H2` in Experiment 22 and all 20 Exp-27 test tasks were scored once in Experiment 27; therefore `exp27_split` is a benchmark comparison on a previously opened test split, not a pristine unseen population.
  2. `cv5_fold`: deterministic stratified 5-fold grouped task partition across all 50 tasks (`fold 0..4`, each fold = 5 old + 5 new tasks = 10 held-out tasks / 35 artifacts, drawn with `numpy.random.default_rng(20261126)` before any run). All model selection, hyperparameter tuning, and scaler/prior estimation happen strictly inside each outer fold's 40 training tasks via nested 4-fold grouped inner CV (`0` prompt demos from any task in `H4` -> `0%` cross-fold prompt leakage).

## 2. Measurement Contract & Karpathy Sanity Controls (Before Scaling)
Before running the 175-artifact `H4` frontier calls or `Qwen3-8B` runs, verify on a smoke suite (`4` non-placeholder training tasks):

| Check / Baseline | Predicted Behavior Before Running | Pass Bar |
|---|---|---|
| Byte-level input hash audit (`175/175`) | Exact SHA-256 match against Exp 100 `items.jsonl` (`ref_ann_sha256`, `py_ann_sha256`, `candidate_sha256`) and Exp 09 `main_rating_task/` + `itemmap.json` | `175/175` matched |
| Positive control: Oracle (gold vs gold) | Expected score `>= 4.5 / 5.0` | Mean `>= 4.5` |
| Negative control: Blank candidate | Expected score `<= 0.5 / 5.0` | Mean `<= 0.5` |
| Negative control: Vacuous `True := trivial` | Expected score `<= 1.0 / 5.0` | Mean `<= 1.0` |
| Negative control: Shuffled candidate (cross-task) | Expected score `<= 1.0 / 5.0` | Mean `<= 1.0` |
| Label-in-prompt reproduction | Given exact target distribution in prompt, return it with Pearson `>= 0.99`, TVD `<= 0.05` | Pearson `>= 0.99` |
| Repeat stability (`k=3`, 15 stratified items) | Low within-item repeat SD (`<= 0.5` on `0-5`) and high `ICC(1,1)` | Measured & reported |
| Calibrator analytic gradient check | Finite-difference vs analytic gradient max error across `M` judges and `K=6` | `< 1e-8` |

## 3. Uniform-Harness Zero-Demo Distributional Prompt (`H4`) & Open-Weight `Qwen3-8B`
- **`H4` prompt:** Exact human rater instructions + the 4 general conventions (zero rated task examples, eliminating all task-demo leakage across folds), requesting A/B/C/D checklist answers, `base_score`, `final_score_0_5`, and verbalized 6-class `score_distribution` over `{0..5}`. Run across all **175** artifacts on at least **2** (target **3**) distinct frontier families under uniform one-turn read-only CLI calls (`$0` API spend):
  - OpenAI `gpt-6-astra` (`high` reasoning, Codex CLI, `~/.codex-vals`),
  - Google `gemini-4-argon-high` (Antigravity `agy` CLI),
  - xAI `grok-4.7` (`high` reasoning, `grok -p`) and/or Anthropic `claude-opus-5-5-high` (`agy` CLI).
- **Open-weight `Qwen3-8B` (free `mercury2` GPUs, `$0`):**
  1. Single-pass next-token logit readout at rating tokens `"0".."5"` (sister-repo Experiment 36 design) on all 175 artifacts + controls; compared against `M=1` argmax one-hot.
  2. Strictly out-of-fold top-4-block LoRA fine-tuning (`r=16`, bf16, sister-repo Experiment 29 design) trained separately with **CE**, **RPS**, and **Pearson correlation** (Priority 2 vs 4 matched-architecture comparison on VeriBench!) on both `exp27_split` and `cv5_fold`, using inner-train validation for checkpoint epoch selection (`<= 6` epochs).

## 4. Candidate Calibrators & Nested Selection Discipline
All non-set-aware primary candidates use **zero set indicator (`old`/`new`)**; a set-aware variant (`+isnew`) is logged strictly as a sensitivity check and never eligible for primary selection:
- `M0_Exp27_F8`: Exact Exp 27 `Ordinal(F8, alpha=0, mix=0)` (baseline).
- `M1_Ordinal_Reg`: Ridge-regularized ordinal cumulative-logit over available judge means.
- `M2_LogitPool_CE`: Multi-judge `(M+K)` logit calibrator (`logits_k = a_k + sum_m tau_m * centered_log(p_m)_k + b1*m_std*u_k + b2*m_std*u_k^2`, regularized toward Dirichlet-smoothed prior `a0`, convex in CE).
- `M3_LogitPool_Unc_CE` & `M3_LogitPool_Struct_CE`: `M2` adding inter-judge disagreement/entropy (`b3 * disp_std * u_k^2`) and observable code/Lean structural features (`thm_ratio`, `excess_thm_log`, `cand_sorry_count_log`, `ident_jaccard`, `edit_similarity`).
- `M4_SimplexTemp_CE` & `M4_SimplexTemp_RPS`: Simplex probability mixture + temperature + class bias fitted by CE or RPS.
- `M5_LogitPool_{RPS,Brier,Pearson}`: Exact `M2` architecture trained by RPS, 6-class Brier, and Pearson correlation surrogate (Priority 2 vs 4).
- `M6_H4_Uniform_CE`: Pure uniform-harness `H4` multi-family `M2` (zero mixed-harness legacy `H2` features).
- `M7_OpenWeight_CE`: Standalone `Qwen3-8B` logit readout + `CE-LoRA` calibrated by `(K+2)` logit calibration.

## 5. Metrics, Decision Rule, and Predictions
- **Primary metric:** normalized `RPS` (per artifact, averaged equally across artifacts).
- **Secondary proper & agreement metrics:** `CE` (`eps=1e-6` renormalization), `TVD`, 6-class `Brier`, `MAE`, signed bias (`mean(E[Q]) - mean(E[P])` with both means), `ICC(A,1)`, `ICC(C,1)`, and secondary correlations `Spearman`, `Pearson`, `Kendall`.
- **Uncertainty:** `10,000`-draw task-cluster bootstrap (`seed=20261126`; plus `seed=20261124` for Exp 27 parity) and paired two-sided bootstrap p-value against the null of zero difference.
- **Decision rule on `exp27_split` (20 test tasks) and `cv5_fold` (50 OOF tasks):**
  - **Works:** Pooled test/OOF `RPS` difference vs set-aware constant has 95% CI strictly `< 0`, point `CE` and `TVD` are lower than the set-aware constant, AND paired `RPS` vs Exp 27's `F8` judge is `< 0` (`cv5_fold` OOF CI `< 0` is the cleanest 50-task test).
  - **Promising:** All proper-score point estimates beat the constant and Exp 27 `F8`, while one or more 95% CIs cross `0`.
  - **Not found:** Otherwise.
- **Pre-registered predictions:**
  1. Updating 247 -> 250 ratings alone changes Exp 27 `F8` by `< 0.005` RPS.
  2. Combining uniform-harness multi-family `H4` + `Qwen3-8B` single-pass logits/LoRA in `(M+K)` logit-pool CE calibration lowers held-out `RPS`, `CE`, and `TVD` vs Exp 27 `F8` and pushes the 50-task OOF `RPS` CI below the set-aware constant.
  3. On VeriBench (`K=6`), CE- and RPS-trained heads/LoRA substantially outperform Pearson-trained heads/LoRA on `CE`, `RPS`, `TVD`, and `Brier`, even when Pearson matches expected-score correlation.
  4. Single-pass `Qwen3-8B` token-logit readout beats `M=1` argmax one-hot on `CE` and `RPS`.

## Amendment 1 (11-26-2026, before any H4 or GPU run)
- **Track 4B open-weight GPU lane on `mercury2` (`0..7` idle GPUs only):**
  1. `Qwen3-4B-Instruct-2507` single-pass next-token logit readout over digit tokens `"0".."5"` (plus matched `M=1` argmax one-hot ablation).
  2. `Qwen3-4B-Instruct-2507` strictly out-of-fold top-4-block LoRA (direct linear 6-class head initialized from digit tokens `"0".."5"` `lm_head` weights) trained under three matched objectives (`CE`, `RPS`, `Pearson`) on statement-preserving `<=2560`-token prompts, evaluated on `exp27_split` and across all 50 tasks via `cv5_fold` (comparing Priority 2 vs 4 directly on VeriBench).
  3. `Qwen3-8B` (manual 2-GPU layer split across two idle GPUs) single-pass next-token logit readout over digit tokens `"0".."5"` (plus `M=1` argmax one-hot ablation).
- **Frontier transport parity:** If any shell CLI rejects long `argv` prompts (`max_chars=107,598`), pass the identical prompt text via temporary file/stdin without altering the prompt bytes.

## Amendment 2 (11-26-2026, post-test Mega QA remediation & full deviations log)
Triggered by the 3-stage Mega QA review (`qa_mega_11-26-2026/`); all fixes below are pure CPU post-hoc analyses/disclosures (**labeled post-hoc sensitivity (Amendment 2), not confirmatory**), preserving all raw frontier/GPU receipts and frozen data CSVs verbatim:
1. **Primary hierarchy restored (`PREREG` §4 line 43) & fair Exp 27 comparators:** Global (zero `is_new`, zero set-aware prior) is restored as the Primary comparison (`G9_h4_3fam_q8b_global` on `exp27_test`, H3-free `nested_winner_global` on `cv5_fold`), with set-aware models (`C7_h4_3fam_uncert`, H3-free `nested_winner_set_aware`) logged alongside Exp 27's own set-aware `F9_both_h3_set` (`alpha=0, m=0.25` selected by Exp 27 and `alpha=0, m=0` F8 HPs) and H3-free `F3_both` (`H2 Astra + Opus`, `alpha=0, m=0`).
2. **`AGENTS.md` frontier-model rule disclosure (`N1`):** `AGENTS.md` (`11-14-2026`) forbids small/open-weight models for judge runs unless explicitly authorized. Track 4B (`Qwen3-4B/8B`, replicating sister-repo Exps 29/36 on Brando's explicit sister-repo prompt) and hybrid judges (`G9`, `C9b`, `C10`, plus `C7`/`C8`/`G6` via `judge_std4`) are therefore reported separately from pure all-frontier 3-family judges (`nested_frontier_global`, `frontier_global_selected`, `frontier_set_c7_std3` using `judge_std3`, ZERO Qwen), requiring explicit user ratification for any primary claim involving `Qwen3-8B`.
3. **Exclusion of cached H3 inside `cv5` nested selection:** `C12_hybrid_h3_struct` uses Exp 27 `H3` predictions whose labeled demos and base rate came from Exp 27's training tasks (which cross into Exp 28's `cv5` folds 0–4). `C12` is excluded from `cv5` nested selection (`final_eval_exp28.py`), while the frozen non-test receipt (`results/inner_cv_search_11-26-2026.json`) is preserved untouched as historical log.
4. **Fixed-HP overlap & quarantined LoRA post-cal:** `cv5` fixed-HP rows (`winner_global_fixed`, `winner_set_aware_fixed`, `c9b`) overlap 18/25/24/18/20 items per fold with the 105-item selection set and are quarantined as **exploratory fixed-HP** rows. Leaky `cv5` LoRA `pearson_postcal` (whose 140 training predictions per outer fold came from LoRA checkpoints trained on fold `f`) is quarantined/removed because inner-OOF LoRA predictions were not saved.
5. **Matched-grid `(M+K)` head Priority 2 vs 4:** Original `search_inner_cv.py` searched only `("ce", "rps")` over `alpha in {0.3, 1, 3, 10}`, causing scale-invariant `MKCalibrator(objective="pearson")` to shrink toward uniform (`sd(E) -> 0.0017`, collapsed `RPS=0.2325`). Amendment 2 adds strict-nested matched HP selection over `alpha in {1e-4, 1e-2, 0.3, 1.0, 3.0, 10.0}` for `ce`, `rps`, and `pearson` separately inside each fold (post-hoc sensitivity).
6. **Implementation & provenance deviations disclosed verbatim:**
   - **LoRA config & budget (`run_qwen_gpu_mercury2.py`):** `LORA_RANK = 8` (vs planned `16`), `24` optimizer steps × batch `32` (`768` sample draws = `10.97` epochs at `n=70`, `7.31` at `n=105`, `5.49` at `n=140`, vs `<= 6` epochs planned), `CE` LoRA selected the boundary `steps=24` on all 6 splits; `1` inner validation fold (`(f+1)%5`) used for LoRA checkpoint selection (vs 4-fold inner CV); `train_lora_4b` ran under default SDPA while `sanity`/`extract_4b` forced `SDPBackend.MATH` (low impact at `CHUNK_SIZE=1`, bf16 precision).
   - **Deferred conditions:** `M4_SimplexTemp_{CE,RPS}` and 6-class `Brier`-trained `(M+K)` head were omitted from `distlib.py` (`objective in ("ce", "rps", "pearson")`).
   - **Karpathy label-in-prompt gate (§2):** `5/5` models passed all 4 directional mean bars (`oracle >= 4.5`, `blank <= 0.5`, `vacuous <= 1.0`, `shuffled <= 1.0`), whereas `label_in_prompt_pearson >= 0.99` passed for `2/5` (`codex_astra=1.0`, `agy_opus=1.0`) and failed for `agy_argon=0.622`, `grok_47=0.096`, `qwen3_4b=0.940` (models graded the snippet despite injected tags; `agy_argon` and `qwen3` were scaled anyway).
   - **Pre-/post-freeze artifacts & sanity keys:** `results/qwen3_4b_lora_ce_rps_pearson.json` already held unscored `exp27_test_preds` in `b7a1b10` before `94c5cd8` (`FREEZE`); post-freeze commit `df7f6af` fixed `eval_exp27_f8` (`alpha=0, m=0` matching Exp 27 freeze) and Pearson `theta0` init, requiring reruns of `final_eval_exp28.py`; `results/qwen_sanity.json:138-140` retains 3 extended step-0 tolerance keys from GPU verification whose emitter code was not committed to `run_qwen_gpu_mercury2.py`.
