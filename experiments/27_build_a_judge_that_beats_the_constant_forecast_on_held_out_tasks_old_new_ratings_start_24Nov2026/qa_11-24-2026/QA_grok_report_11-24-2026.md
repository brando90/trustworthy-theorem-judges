# Experiment 27 independent numerical QA — 2026-11-24

Headline arithmetic passes at three decimals. The paired RPS interval against the set-aware constant includes zero, so the verdict remains **promising, not works**. One wording correction: artifacts have 2–4 human ratings, mostly 2–3; one test artifact has four. Scores do not change.

| Test subset | Forecast | RPS | CE | TVD | Spearman (secondary) | Pearson (secondary) |
|---|---|---:|---:|---:|---:|---:|
| pooled | final_Q | 0.075070 | 0.969504 | 0.354948 | 0.894325 | 0.909365 |
| pooled | constant_set | 0.109965 | 1.188888 | 0.478664 | — | — |
| pooled | constant_pooled | 0.170697 | 1.508718 | 0.602990 | — | — |
| pooled | uniform | 0.230952 | 1.791759 | 0.733333 | — | — |
| pooled | h2 | 0.100238 | 4.115286 | 0.330953 | 0.898860 | 0.897586 |
| old | final_Q | 0.134885 | 1.569246 | 0.490030 | 0.895215 | 0.874230 |
| old | constant_set | 0.179711 | 1.793773 | 0.658120 | — | — |
| old | constant_pooled | 0.261913 | 2.158265 | 0.716416 | — | — |
| old | uniform | 0.175926 | 1.791759 | 0.677778 | — | — |
| old | h2 | 0.190926 | 7.681911 | 0.583333 | 0.829154 | 0.861026 |
| new | final_Q | 0.030209 | 0.519698 | 0.253637 | 0.648453 | 0.938230 |
| new | constant_set | 0.057656 | 0.735224 | 0.344072 | — | — |
| new | constant_pooled | 0.102285 | 1.021558 | 0.517920 | — | — |
| new | uniform | 0.272222 | 1.791759 | 0.775000 | — | — |
| new | h2 | 0.032222 | 1.440317 | 0.141667 | 0.717924 | 0.926208 |

## Paired differences: final judge minus baseline

| Baseline | Metric | Difference | 95% task-bootstrap interval |
|---|---|---:|---|
| final_minus_constant_set | RPS | -0.034895 | [-0.075959, 0.002444] |
| final_minus_constant_set | CE | -0.219384 | [-0.458774, 0.009236] |
| final_minus_constant_set | TVD | -0.123716 | [-0.204913, -0.055366] |
| final_minus_h2 | RPS | -0.025168 | [-0.049292, -0.005410] |
| final_minus_h2 | CE | -3.145782 | [-4.973875, -1.579689] |
| final_minus_h2 | TVD | 0.023996 | [-0.058767, 0.099134] |

## Findings and limits

- All 63 comparisons (45 point estimates and 18 paired point/interval endpoints) match the published result at three decimals. Maximum absolute numerical difference: 2.8020675e-06. Small H2 discrepancies come from applying the probability floor to counts before normalising in Grok’s code; the independent local implementation floors the normalised histogram. Neither changes a reported three-decimal value.
- Task bootstrap: 10,000 draws, seed 20261124, sorted task IDs, whole-task resampling, artifact-equal means accounting for task sizes. The code derives all scores from the anonymised input, without expected results in its prompt.
- Counts: train old 30 artifacts/10 tasks, new 40/10; validation old 15/5, new 20/5; test old30/10, new40/10. Total 175 artifacts/50 tasks; test 70/20.
- No task ID crosses splits; no artifact lacks human ratings; no duplicate artifact IDs; all ratings in 0–5; test forecast probabilities are finite, nonnegative, six bins, and sum to 1 within 2.23e-16.
- Ratings wording correction: all artifacts comprise 85 with 2 ratings, 88 with 3, 2 with 4. Test comprises 35 with 2, 34 with 3, 1 with 4. The four-rating test artifact is native-heavy-11-11-2026__item030; the validation artifact is item076. Both have [5,5,5,5]. Rater identities are absent, so distinct-rater/duplicate-response provenance cannot be checked.
- Grok-authored ordinal refit converged: train+val CE 0.949774046; test RPS 0.075070732, CE 0.969502172, TVD 0.354953320. Maximum absolute score difference from frozen forecasts is 5.038997e-06. A separate analytic-gradient, three-start implementation also converged and reproduced scores to three decimals.
- The final judge is not better on every metric: pooled TVD 0.355 versus H2’s 0.331; paired TVD interval includes zero. The new-set TVD point estimate is 0.254 versus H2’s 0.142.
- Not covered by this anonymised input: edit-distance baseline (no feature or predictions supplied), original raw-data authenticity, chronological evidence for pre-registration/freeze, upstream train/test reuse or semantic duplicates beyond task IDs, and repeatability across future human-rating waves. No judge model inference was rerun.

## Model, harness, execution

- Requested heaviest lane: Cursor CLI / grok-4.7-high / personal-cursor. Two requests timed out at 180 s and 600 s with no numerical answer. Neither is counted as completed QA.
- Completed fallback: native Grok CLI, configured model grok-4.7, low effort, personal-grok included-usage lane. Native response usage identifies grok-4.7-build. Started 2026-11-24T22:46:15.761304Z, finished 22:47:55.338207Z; receipt status completed, return code 0. Dashboard reading before fallback: 11.65763855% weekly used, additional usage $0 and credit balance $0. No billing settings were changed.
- Grok explicitly said: “This session is read-only, so I cannot execute the script or check `qa_result.json`.” It supplied the complete standalone Python. The caller extracted and ran that 159-line script unchanged on the anonymised input using the local sci Python environment; execution returned 0 and produced qa_result.json. This is independent model-authored recomputation with caller execution, not native Grok code execution.
- Script SHA256: ded7464308438a9fc280f6712d968be13967630906ae7d1c3af79ab058373ef2. Input SHA256: 67b8dde95cb0fc32d23f7522fa325103c6aa33b9fdf94b308e61c3805116bad9.

## Evidence files

- scratch/AT-3499/grok/qa_recompute.py, qa_result.json, grok_execution.txt, grok_execution.err: unchanged Grok code and execution.
- scratch/AT-3499/grok_response.md, grok-launch.verified.json, grok_comparison.json: model response, route receipt, comparison.
- scratch/AT-3499/independent_numbers.json, independent_refit.json, schema_check.json: separate local checks.
- scratch/AT-3499/cursor-extended-receipt.json: failed high-effort request. No repository or Google Doc edits made by this QA task.
