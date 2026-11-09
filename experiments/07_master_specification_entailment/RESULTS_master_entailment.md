# Results: statement-only master-specification entailment

**Execution complete; parent review and publication to main pending.**

All 48 prespecified primary calls have terminal receipts. The held-out test contains 16 controls from two task/representation families: 12 eligible implications and 4 ineligible cases. The model returned 12 valid probabilities on eligible test cases and abstained on 3/4 ineligible test cases.

This is a constructed feasibility set. Positive labels have checked implications plus satisfiability witnesses; negative labels have checked countermodels. These results do not validate a judge on natural generated artifacts, human ratings, unseen solver models, or imperative equivalence.

## Common held-out test metrics

Every eligible test case remains in the denominator. Values are estimates [95% family-bootstrap percentile interval], using 2,000 draws over only two test families. Intervals collapse when both families have identical observed outcomes; this is not evidence of certainty on new families. These intervals are descriptive and cannot establish population generalization; p-val=n/a. Binary log loss clips probabilities to [1e-6,1-1e-6]. Brier loss uses the binary convention (p-y)^2. Bias is prediction minus label.

| System | Brier | Log loss | Mean absolute error | Bias |
| --- | --- | --- | --- | --- |
| raw | 0.000000 [0.000000, 0.000000] | 1.000e-06 [1.000e-06, 1.000e-06] | 0.000000 [0.000000, 0.000000] | 0.000000 [0.000000, 0.000000] |
| constant | 0.250000 [0.250000, 0.250000] | 0.693147 [0.693147, 0.693147] | 0.500000 [0.500000, 0.500000] | 0.000000 [0.000000, 0.000000] |
| ce_mapping | 1.000e-12 [1.000e-12, 1.000e-12] | 1.000e-06 [1.000e-06, 1.000e-06] | 1.000e-06 [1.000e-06, 1.000e-06] | -4.972e-15 [-4.972e-15, -4.972e-15] |
| brier_mapping | 1.000e-12 [1.000e-12, 1.000e-12] | 1.000e-06 [1.000e-06, 1.000e-06] | 1.000e-06 [1.000e-06, 1.000e-06] | -5.016e-15 [-5.016e-15, -5.016e-15] |

| System | Pearson | Spearman | Kendall tau-b | Area under ROC curve |
| --- | --- | --- | --- | --- |
| raw | 1.000000 [1.000000, 1.000000] | 1.000000 [1.000000, 1.000000] | 1.000000 [1.000000, 1.000000] | 1.000000 [1.000000, 1.000000] |
| constant | undefined | undefined | undefined | 0.500000 [0.500000, 0.500000] |
| ce_mapping | 1.000000 [1.000000, 1.000000] | 1.000000 [1.000000, 1.000000] | 1.000000 [1.000000, 1.000000] | 1.000000 [1.000000, 1.000000] |
| brier_mapping | 1.000000 [1.000000, 1.000000] | 1.000000 [1.000000, 1.000000] | 1.000000 [1.000000, 1.000000] | 1.000000 [1.000000, 1.000000] |

ROC means receiver operating characteristic. Constant-input correlations are undefined, never replaced with zero.

| System | Mean prediction / mean label | Accuracy | Precision | Recall | Cohen kappa | TP/TN/FP/FN |
| --- | --- | --- | --- | --- | --- | --- |
| raw | 0.500000 / 0.500000 | 1.000000 | 1.000000 | 1.000000 | 1.000000 | 6/6/0/0 |
| constant | 0.500000 / 0.500000 | 0.500000 | 0.500000 | 1.000000 | 0.000000 | 6/0/6/0 |
| ce_mapping | 0.500000 / 0.500000 | 1.000000 | 1.000000 | 1.000000 | 1.000000 | 6/6/0/0 |
| brier_mapping | 0.500000 / 0.500000 | 1.000000 | 1.000000 | 1.000000 | 1.000000 | 6/6/0/0 |

TP/TN/FP/FN are true positives, true negatives, false positives and false negatives at probability >=0.5. The full machine-readable analysis includes uncertainty for each defined statistic, common-valid-subset metrics, and paired Brier/log-loss differences from the constant.

## Selection and denominators

The constant is the eligible training-label prevalence. Each fitted mapping uses sigmoid(a+b*logit(p)), with coefficients fitted only on valid eligible training outputs. Four fixed regularization strengths are compared on validation for each fitting loss. Ties choose stronger regularization. The selection receipt precedes all test calls.

| Mapping | Training loss | Selected ridge | a | b | Validation selection loss |
| --- | --- | --- | --- | --- | --- |
| brier | brier | 10.0 | -4.939e-09 | 1.000000 | 1.000e-12 |
| ce | ce | 10.0 | -5.000e-09 | 1.000000 | 1.000e-06 |

| Split | Manifest / eligible / ineligible | Valid eligible probabilities | Ineligible abstentions | All-call statuses |
| --- | --- | --- | --- | --- |
| test | 16 / 12 / 4 | 12 | 3 | {"abstain": 3, "forecast": 13} |
| train | 16 / 12 / 4 | 12 | 4 | {"abstain": 4, "forecast": 12} |
| validation | 16 / 12 / 4 | 12 | 4 | {"abstain": 4, "forecast": 12} |

Failed, invalid or abstained eligible forecasts use the prespecified p=0.5 fallback for raw and fitted pipelines. Ineligible cases have no binary label and are counted separately; they are not scored as ordinary negatives. The report retains best/worst loss bounds for unavailable raw probabilities.

## Observed behavior versus predictions

All 36 eligible controls across the three splits received the correct endpoint probability (0 or 1). This exceeded the prespecified tentative Brier range of 0.12–0.25. Reading all 48 raw responses and verifying every request showed simple, recognizable specifications: identical/equality-reversed definitions on positives and explicit unconstrained-input or wrong-function arguments on negatives. The input audit found no labels, certificates, or truth-bearing IDs in requests. This ceiling result is explained by the constructed set's simplicity; it does not establish calibrated uncertainty on harder inputs.

The model abstained on 11/12 ineligible controls overall and 3/4 on test. On test case c_b6ed7390d1cc (Boolean pair swap with a jointly inconsistent candidate), it returned status=forecast and probability=0 even though its reason explicitly identified inconsistency and repeated the instruction to abstain. The strict parser retained the returned status; the rationale was not used to repair the response. This is an observed eligibility/instruction-following failure, not a semantic negative label.

Every returned probability was 0 or 1 (37 probabilities including that ineligible response); the other 11 responses abstained. All six identical-input proof-body pairs returned equal probabilities, with two-call sample standard deviation 0. The mappings cannot improve raw zero Brier loss on eligible controls; their approximately 1e-12 Brier loss comes from the fixed clipping and fitting procedure. There is no useful evidence here that cross-entropy fitting is better than Brier fitting, or that either improves the raw judge.

## Calls, certificates and repeatability

The run used 48 primary calls, 1 preflight call, and 0 transport diagnostics, with 18203 prompt tokens and 3191 generated tokens reported by the local server. Provider charges: $0. Each call was capped at 2,048 generated tokens and 120 seconds; no reserved call was retried.

The checker compiled 42 supported statements and accepted 60 exact-goal kernel audits: implications plus satisfiability for positives, countermodels for negatives, and inconsistency proofs. Six unsupported axiom declarations were excluded before assigning a semantic label. Nine certificate tests and seven forecast/scorer tests passed. See [certificate report](CERTIFICATE_REPORT.md) for source hashes and the checker trust boundary.

There is one forecast per manifest row. Six proof-body pairs have identical statement inputs by construction; the analysis records their probability differences and two-call sample standard deviations. This is duplicate-prompt variation, not a test with visible proof bodies. Independent repeated forecasting was not measured. Human inter-rater agreement is inapplicable because these are certificate labels, not human ratings.

## Interpretation and next evidence

The model and fitted mappings are assessed on a small, balanced, author-constructed set with simple specifications and eight recurring control templates. Task families are disjoint, but control templates recur across splits. Duplicate-input controls reduce effective diversity. The oracle itself is supplied among the positive controls. Strong performance here would show pipeline feasibility only. The benchmark-construction review by the parent remains pending.

The next scientific evidence is an independently assembled, certificate-labeled natural-output set with more held-out task families and solver identities, retaining unresolved cases. Fresh human returns were not verified from cloud sources, so no claim about their presence or absence is made. VeriBench experiment169/171 remains separately owned; this pilot does not change its scorer, references, or pending outcomes.

The local model is Qwen/Qwen3.6-27B at pinned revision 6a9e13bd6fc8f0983b9b99948120bc37f49c13e9, direct response with thinking disabled, bfloat16, vLLM 0.17.1. The [route record](MODEL_SELECTION.md) documents that the official card recommends a newer serving version and that unrelated model-card benchmarks do not validate judging quality.

Reproduce from [README.md](README.md). Per-item probabilities and statuses are in [scored rows](results/scored_rows.json); sanitized request/response hashes and token accounting are in [forecasts](results/forecasts.json). [Analysis](results/analysis.json) contains every reported metric and uncertainty calculation; [selection](results/selection.json) records fitting and validation. Runtime requests/responses remain outside tracked files.
