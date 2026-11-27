Stage 1 found blocking leakage and reporting errors. The numerical computations reproduce, but several evaluations do not satisfy the claimed strict nesting.

Audited `5e5d3ff4e0a503031366bd36841a74ea374be552..df7f6afb8c5a74f101450fe175518907a266f385`. **Read-only: all 38 tracked files in scope remain unchanged.** No GPU inference, Lean checking, or differential testing was performed.

Below, experiment-relative paths refer to [Experiment 28](/Users/brandomiranda/trustworthy-theorem-judges/experiments/28_multi_family_distributional_judge_and_open_weight_lora_on_new_ratings_start_26Nov2026); JSON paths refer to `results/final_results_11-26-2026.json` unless stated otherwise.

**Verification coverage**

| Requirement | Audit result |
|---|---|
| Commit sequence | Confirmed: `0414a74` 15:54:15 → `7855746` 15:58:53 → `b7a1b10` 17:02:23 → `94c5cd8` 17:03:46 → `df7f6af` 17:26:14 PST. Local execution timestamps support this sequence; immutable evidence proving “evaluated once” is missing. |
| Search excludes test | Confirmed at `scripts/search_inner_cv.py:102`: `load_bundle(include_test=False)`, returning **105 artifacts / 30 tasks**, excluding **70 artifacts / 20 test tasks**. Cached-feature leakage remains, detailed below. |
| Mathematical checks | **5/5 existing tests passed.** Independent CE/RPS/Pearson gradient errors were at most **9.13×10⁻¹⁰**. ICC formulas, categorical-outcome Brier/RPS, unequal-size task bootstrap, and F8 with `alpha=0,m=0` passed independent checks. |
| Qwen implementation | CPU causal-mask/position checks passed; two-pass Pearson gradient relative error **2.74×10⁻¹⁶**. Digit-token assertions and recorded outputs were consistent. Production GPU numerical equivalence was not rerun. |
| Numerical reproduction | Full search replay: **1,017 numerical fields**, maximum difference **2.22×10⁻¹⁶**. Full final-evaluation replay: **2,422 numerical fields, zero differences**, excluding runtime. All writes were intercepted in memory. |
| Report transcription | **779 table-value comparisons passed**, including displayed confidence intervals, means and biases. Freeze settings and metrics match the search receipt. Prose errors remain below. |
| Completeness | All three H4 lanes and both Qwen logit lanes: **175/175**. Each LoRA objective: **175/175** out-of-fold predictions and **70/70** test predictions. Input hashes: **175/175** matched. |
| Privacy | No credential-like matches found in the targeted scan of **36 current files / 122 historical file versions**. **Zero rater identities is false.** |

The nested **global** candidate family excludes the identified H3 leakage: its recorded normalized ranked probability score (RPS) is **0.0704**, with difference versus the constant **−0.0483 [−0.0724, −0.0258]**. This remains useful evidence. Its comparison against F8 crosses zero: **−0.0044 [−0.0098, +0.0012]**.

**Verdict: FAIL**

1. **[CRITICAL] Cached H3 labels contaminate the “strict nested” set-aware evaluation.**  
   `scripts/search_inner_cv.py:30` admits `C12_hybrid_h3_struct`, using H3 predictions generated with labeled demonstrations and a rating base rate from the original Experiment 27 training split. Those labels cross Experiment 28’s new folds. Source: [Experiment 27’s H3 builder](/Users/brandomiranda/trustworthy-theorem-judges/experiments/27_build_a_judge_that_beats_the_constant_forecast_on_held_out_tasks_old_new_ratings_start_24Nov2026/scripts/build_h3_requests.py:49), especially lines 49–57 and 76–90.  
   `$.nested_fold_selections[1].set_aware.candidate` and `[4].set_aware.candidate` select C12. Fold 1’s base rate includes **five held-out tasks**; fold 4 additionally exposes same-fold labeled demonstrations to **35/35 artifacts**. Cached-response hashes and all 175 H3 feature rows were verified. The F8 outer-CV baseline also reuses these features. **Regenerate H3 within each split or exclude it before claiming strict nesting.**

2. **[MAJOR] LoRA Pearson postcalibration indirectly uses outer-test labels.**  
   `scripts/final_eval_exp28.py:344–357` fits fold `f`’s calibrator using other folds’ globally out-of-fold predictions. Their underlying LoRA models trained on fold `f` (`scripts/run_qwen_gpu_mercury2.py:757–781`). Thus **140/140 calibration-training covariates per fold** have a dependency on the held-out labels.  
   Affected JSON: `$.qwen3_4b_lora.cv5_oof.pearson_postcal` and `.ce_vs_pearson_postcal`; affected report: `RESULTS_11-26-2026.md:81`. Their calibration-training predictions must be generated entirely inside each outer training partition.

3. **[MAJOR] Fixed-winner cross-validation retains model-selection leakage.**  
   `scripts/final_eval_exp28.py:181–183,265–273` reuses configurations selected using 105 artifacts when evaluating all 175 artifacts. Outer folds contain **18, 25, 24, 18 and 20** artifacts already used in that selection.  
   Affected JSON includes `$.cv5_nested_oof.winner_*_fixed`, `.c9b_zero_opus_fallback`, `.head_*`, and `$.set_breakdown_cv5`. Fits exclude each outer fold, but configuration selection does not. Consequently, `RESULTS_11-26-2026.md:47`—“Every fold predicts strictly held-out task families”—is false for these rows. Label them exploratory or perform selection inside each outer fold.

4. **[MAJOR] The head comparison does not give Pearson matched hyperparameter selection.**  
   `scripts/search_inner_cv.py:128–133` searches only cross-entropy (CE) and RPS. `scripts/final_eval_exp28.py:270–273` then applies the CE-selected winner’s settings to Pearson. This contradicts the matched validation-RPS selection claim at `RESULTS_11-26-2026.md:67`.  
   Separately, “CE/RPS beat Pearson—Strongly Confirmed” at line 20 overstates the LoRA evidence: test RPS-trained LoRA has **RPS 0.1914 versus Pearson’s 0.1845**, with difference **+0.006871 [−0.004785, +0.018810], p=0.2524**. It is worse on all four reported proper-score point estimates. Sources: `$.qwen3_4b_lora.exp27_test.{rps,pearson}.point` and `.rps_vs_pearson`. CE’s advantage should be reported separately.

5. **[MAJOR] Material preregistration deviations lack an amendment.**  
   - `PREREG.md:43` excludes set-aware candidates from primary selection; `FREEZE_11-26-2026.md:13` promotes C7 to **Primary**.
   - `PREREG.md:17` requires four-fold inner cross-validation for selection; `scripts/run_qwen_gpu_mercury2.py:757–774` uses one inner validation fold per outer fold.
   - `PREREG.md:40` specifies LoRA rank **16**; the implementation sets **8** at `scripts/run_qwen_gpu_mercury2.py:39`.
   - Planned simplex-temperature and Brier-training conditions (`PREREG.md:48–49`) are absent from the implemented search; `scripts/distlib.py:230` only accepts CE/RPS/Pearson.  
   
   Amendment 1 does not document these changes. **175/175 prediction completeness does not establish completion of the preregistered comparisons.**

6. **[MAJOR] “All controls passed” contradicts the preregistered gate.**  
   [LaTeX fragment:55](/Users/brandomiranda/trustworthy-theorem-judges/latex/results/28_multi_family_distributional_judge.tex:55) claims all five models passed. `PREREG.md:29` requires label-reproduction Pearson **≥0.99**. In `results/karpathy_controls_11-26-2026.json`, these fail:
   - `$.agy_argon.label_in_prompt_pearson = 0.621678`
   - `$.grok_47.label_in_prompt_pearson = 0.095663`
   - `$.qwen3_4b.label_in_prompt_pearson = 0.939974`  
   
   Interpreting failures as resistance to injected labels does not satisfy the registered criterion.

7. **[MAJOR] Two F8 prose values are stale and exaggerate improvement.**  
   `RESULTS_11-26-2026.md:62–63` quotes old/new F8 RPS **0.1603 / 0.0694**. Final values are **0.1243 / 0.0376**, at `$.set_breakdown_cv5.{old,new}.exp27_f8.RPS`. The incorrect values reproduce the superseded `alpha=1,m=0.10` implementation exactly.  
   Additionally, line 19 combines fixed/nested-set-aware RPS values with CE and total variation distance (TVD) values from different model rows. For its stated RPS pair, corresponding CE is **0.922/0.918**, and TVD is **0.346/0.342**.

8. **[MAJOR] “Zero rater identities” is demonstrably false.**  
   Participant IDs remain in `PREREG.md:13`, `RESULTS_11-26-2026.md:25`, `scripts/build_data_11_26.py:52,61,115`, and the `freeze` field of **all 100 rows** in `data_11-26-2026/human_ratings_new_11-26-2026.csv:2`. A literal participant name also appears in historical `PREREG.md:13` from `0414a74` through `94c5cd8`, removed only in `df7f6af`. This contradicts `RESULTS_11-26-2026.md:26`; current-file cleanup cannot establish historical absence.

9. **[MINOR] Freeze/execution claims exceed the available evidence.**  
   Commit ancestry and local timestamps support preregistration → inference → raw-result landing → search → freeze → final results. They do not prove **one** evaluation. The final commit changes Pearson initialization and F8 parameters; final-result files have distinct creation and overwrite timestamps, and prose retains the superseded baseline’s results. Sources: `FREEZE_11-26-2026.md:32`, `scripts/distlib.py:330`, `scripts/final_eval_exp28.py:124`, and the `df7f6af` diff.  
   Also, CV5 LoRA had already used `exp27_split=test` labels under its separate training/validation partitions before the freeze. That does not establish direct leakage into the Exp27 fitted judge, but “before any held-out test call” at `RESULTS_11-26-2026.md:6` is too broad.

10. **[MINOR] Bootstrap p-value precision is overstated.**  
    `scripts/distlib.py:206–208` reports twice the smaller bootstrap sign fraction. Zero opposite-sign draws out of 10,000 becomes zero, displayed as `p<0.0001`. Report the tail count and approximate method; this simulation does not certify that population-level bound. The confidence-interval calculations reproduced correctly.

11. **[MINOR] Two provenance labels need correction.**  
    `h4_3fam_only` at `scripts/final_eval_exp28.py:222` consumes Qwen information through `judge_std4`, defined from four models at `scripts/data_exp28.py:161–162`. It is not H4-only.  
    Separately, `results/qwen_sanity.json:138–140` contains three additional equivalence checks absent from the committed implementation. `scripts/run_qwen_gpu_mercury2.py:555–568` records only a logit discrepancy and asserts no tolerance. This is missing reproducibility evidence, not a demonstrated masking error.

12. **[MINOR] Committed report sources omit Experiment 28.**  
    [mega_tech_report.tex:15](/Users/brandomiranda/trustworthy-theorem-judges/latex/mega_tech_report.tex:15) includes `mega_results`. At audited `HEAD`, committed `latex/mega_results.tex` ends at Experiment 27, and `latex/mega_meta.tex` still declares four results dated 11-24-2026. Experiment 28 appears only in the pre-existing dirty generated sources, while the updated PDF was committed. Commit the corresponding generated sources after reconciling the existing work.