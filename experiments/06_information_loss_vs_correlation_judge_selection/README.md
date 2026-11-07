# Information losses versus correlations for judge selection

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/06_information_loss_vs_correlation_judge_selection/README.md>

**TLDR:** Compare the objective used to choose or fit a judge while holding data, candidate capacity and search budget fixed. Evaluate every resulting judge with the same held-out probability and correlation metrics. Both cached-data conditions are complete; [RESULTS.md](RESULTS.md) reports their findings and limitations.

Created 11-06-2026 at Brando Miranda's request; executed on the Vals/work continuation with a deterministic CPU job on Stanford skampere3. The frozen primary histogram comparison and the separate matched probability-head follow-up completed with zero new model calls. The primary comparison did not resolve a cross-entropy selection advantage; the head comparison has a substantial Pearson nonconvergence limitation. See the full report before interpreting either result.

## Question and predictions

Does choosing or optimizing a judge using cross-entropy (CE), forward Kullback–Leibler divergence (KL), Brier loss, or ranked probability score (RPS) improve held-out agreement compared with Pearson-, Spearman-, or Kendall-based selection?

The useful comparison is an **objective-by-evaluation-metric matrix**, not a separate table reporting each arm only under its own objective. The study may find tradeoffs, ties or failures; an information objective need not win every metric. Existing theory already justifies proper scores for distribution prediction, so novelty of this particular empirical comparison is not established without a literature search.

Predictions before execution: CE-selected judges may improve held-out CE relative to correlation-only selection; improvements in Brier or rank correlations are uncertain. Brier and RPS are proper-loss baselines, not correlation baselines. With identical item weighting, targets and numerical treatment, CE and forward KL select the same candidate and must not be counted as independent experimental evidence. Synthetic checks can establish identities and counterexamples, not empirical superiority.

## Target and units

For artifact i=(task, solver, generation), predict a six-category probability mass function q_i over human ratings 0,...,5, conditioned on Python source, candidate formal specifications and gold reference. Formal specifications are unproved theorem statements. Each available human rating is an observation, not a distribution known without error. Average proper losses over raters within an artifact, then artifacts within task, then tasks, to avoid overweighting tasks with more outputs or raters. Record all denominators and missingness. Preserve a secondary artifact-weighted analysis if needed for comparison to earlier work.

Use empirical per-artifact human frequencies p_hat_i only where individual ratings are available. Sparse frequencies from two or three raters are noisy; zeros do not establish zero population probability. A scalar mean or a normalized 0–5 model score does not determine a six-category distribution. Native probability outputs, histograms of repeated sampled ratings and training-fitted scalar-to-distribution mappings are distinct conditions. Do not silently substitute one for another.

The separate binary prover target from experiments 03/04 may support a secondary exploratory reproduction. It is not human agreement. Experiment 05's three all-zero outcomes cannot establish objective superiority or rank performance.

## Cheapest execution: fixed candidate selection

1. Inventory cached raw human ratings and saved judge outputs; audit item/source hashes, task families, model identity, missingness and prior split exposure. Use existing already-open historical evidence; do not open sealed fresh human ratings.
2. Before scoring outcomes, freeze a shared finite pool of candidate forecasts and deterministic tie-breaking. Native probability candidates are preferred where available. For repeated scalar caches, use the same declared repeated-rating histogram estimator first. Training-fitted, limited-capacity distribution heads are a separate secondary condition; label them fitted mappings rather than end-to-end language-model training.
3. On the same inner validation tasks, select one candidate per objective: CE/forward KL (one arm), multiclass Brier, normalized RPS, Pearson, Spearman, Kendall tau-b, and the user's empirical weighted squared probability loss. Total variation distance (TVD) may be an exploratory selection arm. Correlations operate on q_i's expected rating versus the human mean, never on flattened probability coordinates.
4. Evaluate every selected candidate on the same outer held-out task families under all listed metrics. Report selection frequency and when objectives choose the same candidate. Test outcomes must never influence the candidate pool, mapping parameters, tie-breakers or chosen objective.

Proposed historical design: five outer task-family folds, four inner task-family folds, seeds 11062026 through 11062030; reduce folds before scoring if the audited number of families cannot support them. Preserve original train/validation/test as a separately reported retrospective sensitivity analysis. Repeated resplits do not create new independent tasks or erase historical exposure. Retained candidates trained on these same ratings must have their exposure disclosed; nesting a new mapping does not erase upstream leakage. Freeze eligible candidate rules before comparing performance.

## Secondary execution: matched optimization

Fit the same small probabilistic model/head with the same features, architecture, initializations, regularization choices and tuning budget under different losses. Compare CE, Brier and RPS directly. For correlation objectives, declare whether exact finite candidate selection or a differentiable surrogate is used; optimizing a surrogate is not optimizing exact Kendall/Spearman. Keep the objective used for fitting separate from the objective used for validation selection; use a small factorial or clearly separate phases rather than confounding both changes. A monotone remapping cannot improve Spearman/Kendall without changing ties/order, an essential control. Neural fine-tuning is a later condition only if caches cannot answer the first question and matched runs can finish within verified resources.

## Common evaluation matrix

Rows are selection/training objectives; columns are held-out:

- CE/log loss (natural logs; lower better) and forward KL(p_hat || q), with human target entropy shown separately.
- Multiclass Brier = sum over six categories of (q_r - 1{R=r})^2, range [0,2]; use this convention everywhere.
- Normalized RPS = (1/5) sum over thresholds 0,...,4 of (CDF_q(k)-1{R<=k})^2, range [0,1].
- Pearson r, Spearman rho and Kendall tau-b between expected rating and human mean. Report undefined constant cases and ties, not zero correlations.
- User-weighted squared PMF distance sum_r p_hat_r (p_hat_r-q_r)^2, and TVD = 0.5 sum_r |p_hat_r-q_r| as noisy distribution diagnostics.
- Mean absolute error, signed bias (judge expected rating minus human mean, both normalized by 5), both means, missingness and failure counts.

Use q_epsilon=(1-6*epsilon)q+epsilon with epsilon=1e-6 for the primary finite-log implementation; disclose the transform and predeclare sensitivity epsilons 1e-8 and 1e-4. Do not smooth human test targets as if unseen rating categories were observed. Natural zero forecast mass on an observed category would yield infinite unmodified log loss; report its count. Reuse identical normalization/weights for the CE–KL identity.

Primary contrast: CE selection minus Spearman selection on held-out mean CE. Secondary contrasts include RPS/Brier selection and correlations; do not choose the primary contrast after looking at results. Give paired task-family uncertainty and 95% intervals. Full recipe resampling must redo fitting/selection; a bootstrap of fixed out-of-fold predictions excludes selection/training uncertainty and must be labeled accordingly. Do not treat folds, seeds, raters on one artifact or solver outputs on one task as independent sample-size multipliers. Report conditional and full-recipe uncertainty separately if both feasible, with a bounded budget frozen first. Do not infer generalization to unseen raters or solver families without the corresponding held-out analysis.

Ranking human ratings is not the same target as a distribution over rankings. Primary target here remains six-category ratings. If genuine pairwise preferences/ranking observations exist, add a separately defined ranking experiment; do not fabricate independent preference observations from all overlapping item pairs.

## Execution and artifacts

Start with CPU-only cached-data work; GPUs are unnecessary for the fixed-pool experiment. For an overnight job, the continuation agent should use an eligible persistent Stanford host, verify gateway/access, inspect available resources, and preserve one writer and a bounded watchdog. User authorization covers this work on existing clusters; it does not lift existing measured-inference funding pauses or buy credits. An initial cached-data batch can be capped at eight wall-clock hours, eight CPU threads and $0 provider inference, with per-fold checkpoints and a full declared manifest. Do not consume the entire night if the analysis finishes sooner.

Directory contents: this design; `PROTOCOL_FROZEN.md`/`protocol.json`; `HEAD_PROTOCOL.md`/`head_protocol.json`; `source_audit.json`; `MATH_AND_NOTE.md`; `HANDOFF_VALS_CODEX.md`; `CKPT_objective_comparison.md`; `RESULTS.md`; `DATA_INVENTORY.md`; reproducible import, metrics, fitting, verification and report code in `scripts/`; and aggregate results/terminal receipts in `results/`. This folder remains active for future fresh-human confirmation; the cached conditions are finished. Original image and exact request are preserved in ignored canonical `private/06_information_loss_vs_correlation_judge_selection/inputs/`, with SHA-256 provenance. Keep raw ratings and private solver artifacts there too, never in this public experiment folder.

Reference: Gneiting and Raftery (2007), [Strictly Proper Scoring Rules, Prediction, and Estimation](https://sites.stat.washington.edu/raftery/Research/PDF/Gneiting2007jasa.pdf). It establishes the proper-score framework; it does not establish that CE wins this dataset or every downstream metric.

## New notebook follow-up, 11-07-2026

The [distance extension](followup_11-07-2026/RESULTS.md) adds Wasserstein and Gaussian-kernel selection to the same cached sample; neither resolves an advantage over Spearman. See the [focused literature check](followup_11-07-2026/LITERATURE.md) and [remaining-work prompt](followup_11-07-2026/FOLLOWUP_PROMPT.md). The original selection and fitting conditions remain unchanged.
