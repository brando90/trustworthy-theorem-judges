<!-- TLDR: Study a Bernoulli forecast of bounded prover acceptance as a cheaper alternative research question to modeling human coverage-rating distributions. -->
# Experiment 03: prover-target formal specification coverage judge

**Status, 11-06-2026:** zero-call retrospective execution completed; new model inference remains paused under the existing funding gate. No new language-model forecast was evaluated. An artifact is one solver run on one task. This public project studies the forecasting judge; VeriBench owns the prover metric.

A formal specification is an unproved theorem statement. The proposed judge predicts the probability that a specified bounded prover finds and validates a proof that the candidate specifications imply the reference specifications, usually a conjunction including `Pre -> Post`. A single observed outcome is exactly 0 or 1; a benchmark mean and a predicted probability lie in `[0,1]`. A failed attempt is operational 0, not proof of non-entailment.

The first execution reuses 1,024 historical Tiny256 artifacts and learns a probability map from saved judge-produced formal specification coverage scores to saved five-condition prover acceptance. It compares the map with a training-prevalence baseline, with task separation and four leave-one-agent-out fits. The data were previously exposed, and the old acceptance rule includes candidate-proof checks, so this is a retrospective feasibility result rather than a fresh statement-only judge validation.

- [Results](RESULTS.md): aggregate metrics and uncertainty, generated from saved receipts.
- [Protocol](PROTOCOL.md): estimand, Brier loss, splits, controls, limitations and smallest future pilot.
- [Source audit](SOURCE_AUDIT.md): actual prover implementation, historical gates and integrity gaps.
- [Runbook](RUNBOOK.md): exact reproduction commands and private/public boundaries.
- [Forecast prompt](prompts/binary_forecast.md): explicit probability of protocol acceptance.
- [Source hashes](sources/provenance.json), [configuration](config.json), [checkpoint](CKPT_prover_target.md).

No human-rater count is required for this operational target. That cost reduction changes the scientific question: predicting proof-search success does not establish agreement with experts or semantic entailment on every unresolved artifact. A possible workshop/thesis contribution is a cheaper probabilistic predictor with credible transfer and integrity evidence, rather than a claim that the human study is unnecessary.

**TLDR-end:** [ttj: prover-target study] The experiment has a reproducible no-new-call analysis and a separate plan for a faithful fixed-goal forecasting target. Human-rating prediction and prover-outcome prediction remain distinct studies.
