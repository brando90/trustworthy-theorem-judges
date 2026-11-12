<!-- TLDR: A probability map of historical coverage ratings predicts historical prover acceptance better than a prevalence constant; this is retrospective operational forecasting only. -->
# Experiment 03: retrospective prover-target results

On 512 historical test artifacts from 128 tasks, a fitted probability map improves Brier loss over the training-prevalence baseline by -0.058 [-0.087, -0.031] (mapped minus constant; negative is better; p-val=n/a).

This is a zero-call reanalysis of the archived Tiny256 condition, not a new VeriBench release evaluation, a fresh judge test, or semantic entailment validation. The target is experiment 145’s saved five-condition acceptance flag. Existing outcomes had prior exposure, task-family separation is unverified, and bridge faithfulness remains unverified.

## Scope and selection

Source join: 1024 artifacts, 256 task identities, four historical solver configurations, 0 missing joins. Hash split: 64 train, 64 validation, 128 test tasks. The pooled fit has 256 training and 256 validation artifacts. Ridge selected by validation Brier loss: 0.0. Training-prevalence forecast: 0.800781. The test has 405 observed successes.

The map fits logistic log loss on training outcomes, with its ridge strength selected by validation Brier loss. No test refit or threshold search is performed. Historical coverage ratings are input features; they were not elicited as prover-success probabilities. The raw scalar row is a diagnostic numerical comparison.

## Pooled retrospective test

| Forecast | Brier loss ↓ | Mean absolute error ↓ | Bias (forecast − outcome) | Forecast mean | Outcome mean |
|---|---:|---:|---:|---:|---:|
| mapped | 0.107 [0.078, 0.139] | 0.220 [0.189, 0.254] | 0.007 [-0.036, 0.054] | 0.798 [0.762, 0.831] | 0.791 [0.729, 0.852] |
| constant | 0.165 [0.129, 0.203] | 0.325 [0.289, 0.363] | 0.010 [-0.051, 0.072] | 0.801 [0.801, 0.801] | 0.791 [0.729, 0.852] |
| raw_scalar | 0.141 [0.100, 0.185] | 0.171 [0.125, 0.221] | 0.152 [0.104, 0.203] | 0.943 [0.918, 0.965] | 0.791 [0.729, 0.852] |

| Forecast | Pearson | Spearman | Kendall | Area under receiver operating characteristic curve |
|---|---:|---:|---:|---:|
| mapped | 0.596 [0.458, 0.704] | 0.621 [0.473, 0.739] | 0.599 [0.457, 0.712] | 0.799 [0.719, 0.868] |
| constant | unavailable (constant vector) | unavailable (constant vector) | unavailable (constant vector) | 0.500 [0.500, 0.500] |
| raw_scalar | 0.576 [0.460, 0.673] | 0.621 [0.473, 0.739] | 0.599 [0.457, 0.712] | 0.799 [0.719, 0.868] |

## Leave-one-agent-out fitting procedure

Each fit excludes the named solver from both training and validation (192 artifacts per split), then predicts its 128 test artifacts. These are four historical configurations, not random draws of future agents.

| Excluded configuration | Ridge | Mapped Brier | Constant Brier | Paired difference |
|---|---:|---:|---:|---:|
| GPT-6 Astra / Terminus 2 | 0.0 | 0.104 [0.069, 0.141] | 0.158 [0.123, 0.197] | -0.054 [-0.080, -0.030] |
| Opus 5 / Claude Code | 0.0 | 0.136 [0.091, 0.187] | 0.194 [0.147, 0.245] | -0.057 [-0.094, -0.023] |
| GPT-5.6 Sol / Codex CLI | 0.0 | 0.114 [0.072, 0.158] | 0.182 [0.137, 0.232] | -0.069 [-0.118, -0.020] |
| Fable 5.1 / Terminus 2 | 0.0 | 0.092 [0.060, 0.127] | 0.136 [0.102, 0.171] | -0.044 [-0.068, -0.023] |

## Historical acceptance counts

These counts describe source revisions of the operational acceptance rule. They do not measure a new prover, and the five-condition target is not proof-invariant statement coverage.

| Configuration (256 artifacts each) | Raw accepted | Conditions 1–4 | Conditions 1–5 (target) |
|---|---:|---:|---:|
| GPT-6 Astra / Terminus 2 | 212 | 212 | 209 |
| Opus 5 / Claude Code | 213 | 184 | 181 |
| GPT-5.6 Sol / Codex CLI | 199 | 189 | 186 |
| Fable 5.1 / Terminus 2 | 216 | 216 | 213 |

## Uncertainty and limits

- All intervals use 10,000 paired task-clustered bootstrap resamples, seed 11062026, conditional on the fitted models and fixed solver panel. They omit training/selection uncertainty and unverified task-family dependence. Full statistics for every excluded-agent condition are in `results/retrospective.json`.
- p-val=n/a: descriptive retrospective screening, no confirmatory test. Correlations are undefined for the constant forecast. One saved outcome per artifact means repeat-search variance is unavailable.
- The source checker’s name matching and axiom checks do not establish statement/adapter faithfulness. Source experiment 168 found adversarial failures in related checkers. A future predictor can learn such operational artifacts without learning semantic coverage.
- Source labels include candidate-proof axiom filters, representation choices and unbounded historical authoring variability; the exact deployed prover model/effort was not recorded in the source 142 protocol. The `tc` manifest does not bind an exact judge model per artifact. These limitations preclude an exact modern model comparison.
- No human ratings, candidate code, private task identities or per-artifact outputs are exported. The protected source blobs and exact split manifest remain under ignored `private/prover_target/`.
- New measured model calls: 0. Incremental measured-inference cost: $0. Funding pause remains in force; its scoped exceptions were not expanded.

## Decision

The retrospective screening criterion is met: the pooled paired interval is below zero. This supports further study of a cheap operational forecasting target. It does not establish that a new language-model probability judge works, that the target equals semantic entailment, or that the human-rating study can be replaced without changing its question.

Copy-ready collaborator message: “I tested a no-new-call fallback: learn the probability that a fixed prover accepts a specification implication. Historical coverage scores contain useful predictive signal, but the current labels depend on proof and adapter rules, so the next study needs a faithful statement-only protocol and a fresh test.”

**TLDR-end:** [ttj: prover-target study] A zero-call retrospective probability map improves prediction of saved prover acceptance. The deliverable is an operational forecasting feasibility result, not fresh semantic or human validation.
