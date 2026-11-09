# Retrospective RPS versus Pearson mixture results

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/10_retrospective_rps_vs_pearson_mixture/results.md>

**TLDR:** No resolved advantage of normalized ranked probability score (RPS) training over Pearson training on the historical original test split. The paired normalized RPS difference (method 4 minus method 2) is +0.005241, with a 95% refit/reselection family-bootstrap interval of [−0.068074, +0.014864]; 1,998/2,000 draws are valid and p-val=n/a. Lower RPS is better.

Validation selected the RPS-trained mixture, which is retained as the exported practical candidate; the test point estimate favors Pearson. This is retrospective evidence from 30 test artifacts, 10 tasks, nine task families and 78 observed ratings. It does not show that a proper objective is universally better or that a deployable semantic judge has been validated.

Copy-ready collaborator message: “I finished the matched RPS-versus-Pearson comparison on our existing ratings. Validation chose the RPS mixture, but the held-out difference remains uncertain, so we need the new human data for a stronger conclusion.”

## Evidence and scope

The [protocol](PROTOCOL.md), [configuration](protocol.json), code and [hash freeze](FREEZE.json) were published in `d34052eb0ab4272b33dda28f2f8f6cc6cb014c53` before these fits and test scores. This does not erase prior historical exposure: the original test outcomes had already been inspected, task families cross splits, and the same expert columns recur. The [publication eligibility receipt](results/ELIGIBILITY.json) binds configuration, rubric, evaluator, source hashes, missingness and uncertainty. The [machine-readable results](results/results.json) are the numerical authority.

The incoming set-N collection was not read. These are fitted mixtures of five cached configurations, not newly trained or queried semantic LLMs. The original VeriBench public-paper condition and its formal-prover FSC route remain separate. The sister project’s completed [CE-versus-Pearson comparison](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/blob/main/experiments/03_exp06_ce_vs_pearson_matched_budget/RESULTS_comparison.md) is reused as solver precedent, not rerun or overwritten. This experiment adds the missing RPS objective with original-split validation-selected shrinkage.

## Data and matched procedure

| Split | Artifacts | Tasks | Families | Observed human ratings |
|---|---:|---:|---:|---:|
| train | 30 | 10 | 9 | 78 |
| val | 15 | 5 | 5 | 39 |
| test | 30 | 10 | 9 | 78 |
| total | 75 | 25 | 19 | 195 |

There are 195 observed ratings out of 225 artifact-by-expert slots; 30 are missing and are not imputed as zeros. All 75 artifacts have observed ratings. Each of five cached judge configurations contributes three integer ratings per artifact: 1,125/1,125 cached draws, none missing. Individual ratings and forecasts remain private. All 1,478 files in the source hash manifest were verified.

Both methods use the same six-probability histogram representation, simplex mixture, probability floor, training marginal and six-value shrinkage grid. Both select shrinkage by validation normalized ranked probability score (RPS). Each receives five objective fits plus the shared constant case: 12 primary fit requests, ten actual objective fits. Each objective fit allows at most 31 finite-face linear solves; certification replaces arbitrary iteration stopping. All numerical certificates passed. There were 23,976 bootstrap fit requests.

The recorded cached models are `openai/gpt-6-sol-high` at reasoning effort `high`, and `anthropic/claude-opus-5-5-no-fallback` at compute effort `max`. These are historical manifest selectors, not claims about current model availability. H0 mirrors the human rubric, H1 adds training-derived conventions, and H2 adds leave-task-out training demonstrations. All use the historical Vals gateway harness. Full Python, candidate Lean and annotation-era reference Lean files are visible, including any proof bodies/placeholders; this comparison itself only consumes their cached scalar ratings.

## Primary and secondary test results

Scores below are equally weighted over test artifacts, after averaging human observations within artifact. RPS uses five ordinal thresholds; CE is cross-entropy in natural-log units; total variation distance (TVD) compares each prediction with that artifact’s empirical human histogram. These quantities measure different properties.

| Candidate | Validation RPS | Test RPS | Test CE | Test TVD | Pearson |
|---|---:|---:|---:|---:|---:|
| method2_pearson | 0.081657 | 0.137480 | 1.923556 | 0.559829 | 0.859830 |
| method4_rps | 0.073344 | 0.142721 | 2.320076 | 0.563828 | 0.836253 |
| constant | 0.166833 | 0.183611 | 1.805050 | 0.665000 | undefined |
| equal_mixture | 0.104414 | 0.172903 | 6.918247 | 0.596666 | 0.813189 |
| best_cached | 0.105185 | 0.190740 | 9.132987 | 0.672222 | 0.663652 |

`best_cached` was selected on validation as `H0_sol`. `validation_selected` is method 4; its numerical test values equal method 4 above. It is not changed after viewing test results.

The constant marginal has lower CE than either fitted method on this test split, while both methods have lower point-estimate RPS and TVD. This is an observed metric tradeoff, not an additional significance claim.

| Paired difference: method 4 − method 2 | Estimate | 95% refit/reselection interval | Valid / requested draws |
|---|---:|---|---:|
| rps | 0.005241 | [-0.068074, 0.014864] | 1998 / 2000 |
| ce | 0.396520 | [-0.580467, 5.837067] | 1998 / 2000 |
| tvd | 0.003999 | [-0.123981, 0.035477] | 1998 / 2000 |
| brier | 0.044751 | [-0.235950, 0.137462] | 1998 / 2000 |
| pearson | -0.023577 | [-0.074670, 0.207584] | 1960 / 2000 |
| spearman | -0.001134 | [-0.138993, 0.170232] | 1960 / 2000 |
| kendall_tau_b | -0.010038 | [-0.149100, 0.140831] | 1960 / 2000 |
| mae | -0.000634 | [-0.088594, 0.022401] | 1998 / 2000 |
| bias | -0.008054 | [-0.091004, 0.064085] | 1998 / 2000 |

The primary interval includes zero. Secondary intervals are descriptive and are not multiplicity-adjusted; p-val=n/a throughout. For losses, a negative difference favors method 4; correlation has the opposite direction.

| Method | Test RPS with 95% refit interval | Test CE with 95% refit interval | Test TVD with 95% refit interval |
|---|---|---|---|
| method2_pearson | 0.137480 [0.106804, 0.245959] | 1.923556 [1.499309, 7.999899] | 0.559829 [0.454345, 0.726077] |
| method4_rps | 0.142721 [0.104012, 0.200381] | 2.320076 [1.599066, 8.459444] | 0.563828 [0.455892, 0.665248] |
| validation_selected | 0.142721 [0.107925, 0.245689] | 2.320076 [1.659567, 10.448053] | 0.563828 [0.459464, 0.767676] |

These are joint task-family resamples across the original split labels, refitting and reselecting within each draw. They preserve the observed family overlap rather than repair it. Of 2,000 draws, two have no validation artifacts and remain invalid without replacement. The paired correlation panel has 1,960 defined draws; a further 38 have undefined correlation in at least one method. Prompts, model versions, rater identities and the three cached draws are fixed; their uncertainty is not included. This is retrospective sensitivity analysis rather than a fresh population-generalization guarantee. Fixed-prediction intervals are also retained in results.json.

## Additional agreement diagnostics

The mean-score diagnostics use ratings divided by five. Standard deviations below describe variation across artifacts, not repeat-call noise. Human test mean = 0.472222; human test SD = 0.281541.

| Method | Brier | Spearman | Kendall tau-b | MAE | Bias | Judge mean | Judge SD |
|---|---:|---:|---:|---:|---:|---:|---:|
| method2_pearson | 0.881390 | 0.831848 | 0.690093 | 0.163645 | 0.122598 | 0.594821 | 0.219473 |
| method4_rps | 0.926141 | 0.830714 | 0.680055 | 0.163011 | 0.114545 | 0.586767 | 0.258454 |

Brier is the six-category sum, with range [0,2]. Forward KL equals CE minus the same empirical human entropy. Weighted probability-mass-function squared distance, mean-score MSE, normalized RMSE and empirical cumulative-distribution distance are also retained in results.json; these diagnostics do not replace the primary RPS endpoint.

The per-artifact empirical human-disagreement contribution to test RPS is 0.050926. Subtracting it gives the squared cumulative-distribution distance to the empirical human histogram; it is shared across methods and does not affect paired RPS differences.

| Cached configuration | Repeats / artifact | RMS within-artifact sample SD on [0,1] |
|---|---:|---:|
| H0_opus | 3 | 0.054975 |
| H0_sol | 3 | 0.130639 |
| H1_sol | 3 | 0.111555 |
| H2_opus | 3 | 0.049889 |
| H2_sol | 3 | 0.084327 |

These repeat summaries use all 75 cached artifacts and only three draws each. They are descriptive, not high-confidence bounds on future judge variance. The exported mixture is deterministic conditional on those cached histograms; its across-artifact SD should not be mistaken for its rerun SD.

## Exported candidate

The [saved parameters](results/selected_models.json) were written and hashed before test scoring. Candidate order is H0_sol, H0_opus, H1_sol, H2_sol, H2_opus.

| Method | Shrinkage toward training marginal | Mixture weights in candidate order |
|---|---:|---|
| method2_pearson | 0.25 | 0.270210, 0.023584, 0.000000, 0.000000, 0.706206 |
| method4_rps | 0.1 | 0.372685, 0.084584, 0.000000, 0.000000, 0.542731 |

The training marginal is [0.083333, 0.150000, 0.188889, 0.172222, 0.255556, 0.150000]. Use `python3 scripts/predict.py --model results/selected_models.json --ratings /private/input.json --out /private/predictions.json` from this experiment directory. Each input row has `artifact_id` and a `ratings` mapping with exactly three integers for each of the five configuration names. The default method is `validation_selected`. A [replay check](results/export_verification.json) reproduced all 75 saved candidate forecasts exactly. This wrapper does not generate the five upstream forecasts or validate use on fresh artifacts.

## Verification and execution

The run completed in 31.840997 seconds with one CPU thread, zero inference calls and zero provider cost. The PID was not captured. A START notice did not precede this short run; the coordinator records that omission and handles the verified completion notification. The private log is `private/10_retrospective_rps_vs_pearson_mixture/RUN_11-09-2026.log`.

Six deterministic test groups passed, including objective identity, artifact weighting, solver recovery, independent optimization checks, Pearson degeneracy cases and selection isolation. The post-run [verification](results/verification.json) independently reconstructed 450 fitted forecasts and 693 metric entries: maximum probability difference 2.22e−16, metric difference 6.22e−15 and paired-interval endpoint difference 0. Bootstrap fits were not independently rerun.

The original scalar verifier found a rank-only discrepancy: scalar sums and NumPy/BLAS means round mathematically tied scores differently in the last bit. The [verification helper](verification/reconstruct.py) retains independent scalar probability/loss reconstruction but evaluates SciPy correlations on the exact frozen float64 mean arrays. Eleven rank-roundoff cases are recorded. No measured outputs, selection, fitted parameters or frozen code were changed. Average ranks of these exact means are the declared convention; tiny numerical perturbations can change the rank diagnostics.

The [eligibility receipt](results/ELIGIBILITY.json), [fit receipts](results/fit_receipts.json), [bootstrap ledger](results/bootstrap_ledger.json), compressed [bootstrap fit receipts](results/bootstrap_fit_receipts.json.gz), and [checkpoint](CKPT_practical_judge.md) preserve provenance and failure counts. The coordinator synchronized a concise companion section to the [existing Google methodology notes](https://docs.google.com/document/d/1zB-gYk-zU1wToS_E_carGSRGtUcF1NgZ-jWF5t1SJws/edit).

**TLDR-end:** [ttj: practical judge] The matched retrospective comparison and reusable mixtures are complete. The observed primary difference remains unresolved; the validation-selected RPS mixture is preserved for further evaluation without claiming fresh semantic-judge validity.
