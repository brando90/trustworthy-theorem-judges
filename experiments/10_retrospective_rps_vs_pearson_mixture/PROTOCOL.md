# Retrospective RPS-versus-Pearson study definition

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/10_retrospective_rps_vs_pearson_mixture/PROTOCOL.md>

**TLDR:** Compare correlation training (method 2) and proper-loss training (method 4) within one explicitly defined historical probability-mixture family. Select both by validation ranked probability score (RPS); estimate their paired test difference without treating these previously exposed data as fresh confirmation.

## Scope and data

This is a new retrospective condition fixed on 11-09-2026 before its fits and test calculations. Prior reports already exposed these data, including test labels and broad performance. It is not a preregistered confirmatory study. The fixed dataset SHA-256 is in `protocol.json`; its original source is VeriBench commit `be287d9bb2f7bd35ba6db1b8735c9ba10d00eade`, experiment 100. The source file contains 75 artifacts from 25 tasks and 19 task families, with 195 expert observations and three cached scalar ratings for every artifact/configuration. The original split has 30/15/30 train/validation/test artifacts and 78/39/78 expert observations. It preserves the old prompt-development boundary; new folds would not refit historical prompt development.

Five fixed configurations are ordered H0 Sol, H0 Opus, H1 Sol, H2 Sol, H2 Opus. Sol uses the recorded `openai/gpt-6-sol-high` selector and high reasoning; Opus uses `anthropic/claude-opus-5-5-no-fallback`, maximum compute effort and adaptive thinking. They are historical single-call judge samples using original Python, candidate Lean and annotation-era reference inputs, not newly run agent judges. The cache metadata and source import bind this provenance; no new byte-level semantic input audit or theorem/proof execution is performed here. Proof visibility and statement-coverage interpretation retain the source condition rather than becoming a new statement-only condition. No new prompt, solver artifact or human rating is generated.

The upcoming inherited set-N collection remains separate and unopened. Source-file matches and available metadata will be reported; historical source hashes are provenance, not proof of unseen-agent generalization.

## Common probability family and budgets

For artifact i and cached judge j, convert its three ratings to an empirical six-category histogram, floor each entry at epsilon = 0.000001 and renormalize once. Let q_ij be that histogram. Let p_i be the empirical human histogram, preserving each observed 0–5 rating. The training marginal c is the equal-artifact mean of p_i on training only, floored and renormalized with the same epsilon.

The forecast is q_i(w, lambda) = (1-lambda) sum_j w_j q_ij + lambda c, with nonnegative weights summing to one. Both methods use the same five candidates, four free mixture-weight dimensions, and fixed lambda grid [0, 0.1, 0.25, 0.5, 0.75, 1]. The grid was chosen before fitting this condition in response to the earlier study's sparse-histogram weakness; this rationale is retrospective.

- Method 2 maximizes training Pearson correlation between expected forecast ratings and human mean ratings, starting with the stable finite cone-projection solver from the sister repository. A common constant shift and positive rescaling preserve Pearson, so lambda < 1 leaves its objective unchanged. We retain the declared tie rule and let the common validation rule choose lambda; no test calibration is permitted.
- Method 4 minimizes mean individual-rating normalized RPS on training. This equals the mean squared cumulative-distribution distance plus a human-disagreement term independent of the forecast. Enumerate every nonempty simplex face, solve its constrained quadratic, choose the best feasible solution, and require the convex Frank–Wolfe gap to be at most 0.00000001.
- Lambda = 1 is a shared constant baseline available to both pipelines, not an optimization of undefined Pearson. Each method makes five objective fits plus that baseline. There are 31 faces per objective fit, one candidate family, six common validation opportunities, and no random restarts or adaptive search. The supplied numerical certificates must pass for every declared fit; a failure invalidates the procedure rather than dropping its bad configuration.
- Objective ties use minimum support then candidate order as in the upstream solver. Validation RPS ties within 0.000000000001 choose the first grid entry. Both methods see identical rows and probability representations and use identical resource ceilings, though numerical operations differ. Actual work and runtime are recorded.

The whole computation has a 1,200-second wall ceiling and one CPU thread; no paid inference. No stopping or extra search based on test performance. Save selected parameters and their digest before test evaluation. The exported parameters preserve the full training marginal and the chosen weights/lambda.

## Evaluation and practical selection

Every primary loss averages human observations within each artifact, then weights artifacts equally. RPS is primary; cross-entropy (CE, natural logs) and total variation distance (TVD) are secondary. Also report six-category Brier, forward Kullback–Leibler divergence to p_i, human-frequency-weighted squared probability distance, mean-score normalized root mean squared error (nRMSE), mean absolute error, signed bias, judge/human means and across-artifact standard deviations, and Pearson/Spearman/Kendall tau-b. RPS includes human disagreement; root mean empirical cumulative-distribution distance does not. TVD = one half of the L1 distance to p_i, not average distance to point-mass ratings and not TVD mutual information. Sparse p_i is not a known population distribution.

All five cached judges, their equally weighted mixture, the train-fitted constant, and the single cached judge chosen by validation RPS are controls. A practical candidate is selected from the two trained pipelines and the three named controls by validation RPS only; the fixed tie order is in `protocol.json`. Report the selected candidate's test performance without switching to whichever test row looks best. This additional selection is included in bootstrap refits. The main objective comparison remains method 4 minus method 2 test RPS, with no numerical deployment threshold and p-value not applicable.

## Uncertainty, missingness and limitations

Use 2,000 common task-family bootstrap draws with the fixed seed in `protocol.json`. Draw from the 19 observed families, retaining all artifacts and multiplicities and the original split labels. Shared families receive the same bootstrap multiplicity across train, validation and test. Refit both procedures and reselect lambda on each draw. This joint resampling retains observed family dependence and the original leakage; it does not cure that leakage. Test contains nine observed families. Also report intervals conditional on the original fitted models on the same valid draws. Use percentile 95% intervals; retain every invalid/empty/failed draw and do not replace draws. Report the eligible denominator for each interval and every undefined correlation.

Rater identities and historical prompts/candidate samples are fixed; the resampling does not cover new human panels, prompt-development uncertainty, new solver agents, or new batches of repeated judge calls. All three original rater columns recur across splits, and task families overlap across splits. Source tasks are disjoint. The original test was previously inspected. These qualifications prevent a fresh generalization or deployed-judge-validation claim.

The cache supplies all scheduled 75-by-five-by-three scalar forecasts. The runner checks their completeness and the 195 observed human ratings; unobserved rater/artifact entries are absent, not zeros. No fitting failure, malformed observation or missing prediction is silently omitted. Retrospective bootstrap failures retain their reason and affect reported denominators. Existing three-repeat variability is reported per cached configuration; repeatability of new aggregate batches is not measured.

## Predictions and controls fixed before measurement

| Check | Prediction |
| --- | --- |
| Human empirical distribution reproduced | TVD and empirical cumulative-distribution distance approximately zero; RPS equals empirical disagreement, CE equals entropy, Brier equals 1 minus sum p_i squared. The floor makes deviations at most small numerical/floor effects. |
| Unanimous rating at 5, forecast at 0 | RPS approximately 1, TVD approximately 1, Brier approximately 2, normalized mean error approximately 1; floor makes CE finite and large. |
| Equal artifact weighting | One correct artifact with one rating plus one maximally wrong artifact with three ratings gives RPS approximately 0.5, not 0.75. |
| Constant forecast | Pearson/Spearman/Kendall undefined, never silently zero; level and distribution losses remain defined. |
| RPS objective solver | Training RPS no greater than any available simplex vertex at the same lambda, within numerical tolerance; matches an independent constrained optimizer on synthetic distributions. |
| Pearson objective solver | Training correlation no lower than any nonconstant vertex, with the upstream cone certificate; identical nonconstant-lambda optimum up to tolerance. |
| Representable synthetic human distributions | RPS fitting reconstructs the exact distribution up to numerical tolerance. This is an optimizer check, not a real-data claim. |
| Real held-out metrics | The winner is unknown. RPS fitting improves its training objective by construction; no guaranteed test-RPS, CE, TVD or correlation improvement follows. |
| Literal instructions and semantic controls | No new semantic prompt or theorem judgment is executed. Label-in-prompt, vacuity and Lean-proof controls are not newly measured; do not reinterpret numerical controls as semantic validation. |

Trace one training artifact through the exact cached ratings, histogram construction, stored weights and metrics, privately. Verify the final metrics with independent scalar arithmetic and the stored predictions before publication. No individual ratings or predictions are public.
