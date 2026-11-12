<!-- TLDR: Predict an observed bounded proof-search outcome with a Bernoulli forecast; the first execution reuses historical data and claims no fresh validation. -->
# Experiment 03: prover-target formal specification coverage judge

Date: 11-06-2026. Configuration: `config.json`. This protocol is committed before running its statistical analysis. The source reports' aggregate counts were already inspected; this is retrospective, not preregistration of an unseen test.

## Question and decision

Can a cheap forecast predict the outcome of a fixed prover protocol on a candidate/reference pair? If so, an operational forecasting paper is a possible workshop or thesis fallback without collecting human ratings. It would not establish semantic completeness or agreement with experts. This project owns the forecasting study; VeriBench owns its prover metric.

A formal specification (FS) is a theorem statement without its proof. A master correctness statement has the form `Pre -> Post`; multiple public obligations form a conjunction. The historical protocol attempts all public reference obligations, not just one selected correctness theorem.

For artifact `z` and fixed protocol `P`, let `Y_P(z,s)` be 1 if the search with seed `s` returns an accepted certificate within the prescribed budget and 0 otherwise. The binary target is the observed operational outcome. A timeout is operational 0 and semantically unresolved. Infrastructure interruption remains separately recorded; both full-manifest and clean-execution counts are reported. The protocol includes extraction, adapter, proof search, checker, limits and acceptance conditions; changing any one creates a new condition.

The prospective judge outputs `q(z,P) = Pr_s(Y_P(z,s)=1)`. With a deterministic protocol/seed the latent target is a point mass; uncertainty in a forecast is uncertainty about that outcome. With independently randomized repeated searches, `p_P(z)` is a conditional success probability. Repeated judge scores are not automatically samples from this distribution.

The primary loss is Brier loss `(q-Y)^2`, in `[0,1]`. Its conditional expectation is `(q-p)^2+p(1-p)`, uniquely minimized at `q=p`. This is the binary analogue of the human study's proper ordinal loss. Log loss is a secondary prospective measure with its zero-probability handling fixed in advance; it is not computed for historical scalar ratings. See [Gneiting and Raftery (2007)](https://sites.stat.washington.edu/raftery/Research/PDF/Gneiting2007jasa.pdf). Equal numeric ranges or benchmark means do not make human coverage ratings and prover outcomes the same construct.

## Execution 1: zero-call retrospective test

Input: the committed `counted_all5` column from historical experiment 145 and scalar coverage ratings `tc` from experiment 140's manifest, joined one-to-one by run. Preserve all 1,024 artifacts (256 tasks times four solver configurations). No sealed human ratings or private benchmark tasks are read. This is the archived Tiny256 condition; it is not a new current-release evaluation, and historical scores are not recomputed or replaced.

The existing scalar rating was not elicited as a probability of prover success. Use it as a feature in a logistic probability map, fitted using training outcomes. Compare a training-prevalence constant and the raw scalar as a deliberately untrained diagnostic. The raw scalar's squared error is not evidence that it forecasts this event. An oracle `q=Y` and `q=0.5` are implementation controls, not deployable competitors.

Sort task identities by SHA-256 of `split_salt + ':' + task`, allocate 64 train, 64 validation and 128 test tasks, keeping all four artifacts of a task together. Fit a logistic map on the training split; select the nonnegative ridge coefficient from `config.json` by validation Brier loss, then evaluate the chosen training fit once on the test split. Do not refit after selection. Also fit four leave-one-agent-out maps with the target configuration excluded from both training and validation; evaluate only its test artifacts. This tests a fitting procedure on four named historical configurations, not one final judge on arbitrary future agents. Related task families are not resolved in these receipts, so this tests task-identity separation only. It is not a family-generalization claim.

Primary comparison: paired test Brier difference, mapped forecast minus training-prevalence baseline (negative favors the map). The design decision is whether the retrospective 95% interval excludes zero below it; this is an agent-chosen screening criterion, not a sufficiency theorem. Report all four transfer results regardless of direction. Descriptive metrics include Brier loss, mean absolute error, signed bias (forecast minus operational outcome), both means, Pearson, Spearman, Kendall and area under the receiver operating characteristic curve. Report training and validation sizes and selection, not just test results.

Use 10,000 task-clustered bootstrap resamples with fixed seed for test metrics and paired differences; retain all configurations within resampled tasks. Intervals condition on the fitted map, historical protocol and fixed four configurations, and do not include training/selection uncertainty or unknown task-family dependence. Correlations with constant vectors are unavailable. `p-val=n/a`: this descriptive screening analysis has no confirmatory hypothesis test. One saved outcome per artifact gives no repeat-search variance. All historical outcomes have prior exposure; this cannot validate a new judge on an untouched test set.

## Predictions before execution

| Control/forecast | Predicted Brier outcome |
|---|---|
| Oracle `q=Y` | exactly 0 |
| Constant `q=0.5` | exactly 0.25 |
| Outcome complement `q=1-Y` | exactly 1 |
| Literal compliant judge output | finite probability in `[0,1]`; honest uncertainty allowed |
| Invalid probability or duplicate/missing input join | fail before scoring |
| Training-prevalence baseline | test error depends on test prevalence; no fixed promised value |
| Mapped historical scalar | direction relative to baseline unknown; this is the empirical question |

## Prospective target: requirements before new inference

Prepare an immutable, kernel-elaborated goal `forall f, A(f) -> G(f)` over shared abstract functions and explicit interface mappings. Candidate theorem proofs are absent. Reference implementation/proofs cannot discharge `G`. A separate certificate must show the candidate assumptions are satisfiable; a theorem `False -> G` alone cannot establish this. Stronger input preconditions must not silently narrow the required reference domain. Function abstraction must include all relevant implementations/helpers or justify fixed vocabulary.

Verify statement transport structurally, not by matching theorem names. A checked proof of the wrong proposition is not evidence about the intended specifications. A trusted checker owns the goal and verifies the submitted proof term against that exact goal, audits transitive axioms using trusted environment data, and rejects forged log messages. Check goal/input hashes and all obligations after execution. Preserve countermodels separately: only a checked witness of `A and not G` establishes non-entailment. Jointly inconsistent candidate specifications are ineligible for semantic coverage credit even though implication is vacuously true.

The statement-only condition must be separate from historical experiment 145: that condition checks axioms of every candidate theorem and therefore changes when candidate proofs change. Candidate satisfiability and target proof acceptance still require valid certificates; proof quality is not substituted for statement coverage. Proof-preserving/statement-preserving controls must test this distinction.

Smallest next measured pilot: 12 new artifact pairs from task families absent from the selected fitting data, balanced across two solver configurations and prespecified positive/negative/representation controls, three independent prover seeds per pair, one forecast per pair (36 bounded searches and 12 forecast calls maximum). This is a feasibility check, not a population test or enough evidence for future-agent generalization. Pin exact versions, effort, token/time/repair caps, extraction/mapping hashes, witness certificates and protected test access before admission. Propose no sample-size sufficiency claim; use observed failure modes and task-level uncertainty to decide a separately versioned larger design.

Funding: current `PAUSE` and `ALLOW` files were read on 11-06-2026; this study is not allowlisted. Measured calls require the existing Vals-funded route or a specific scoped exception. Experiment 168's key exception explicitly excludes other experiments. No pause, cap or failed prior gate is reset. New measured calls admitted here: 0, incremental measured-inference cost $0. A paid pilot estimate is pending an eligible route and exact model; no fabricated quote is supplied. Zero-call analysis, implementation and subscription-based requested review continue.

## Relation to the human study

No human count `H` is needed to learn the operational target. Its randomness is task/solver/search variability, not rater variability. An ordinal human target can give partial coverage credit where a conjunction proof fails; a binary all-obligation target loses this distinction. A forecast can accurately predict prover failures caused by representation or budget and still be a poor semantic coverage judge. Neither result replaces human validation of human-rating predictions. A later paired study may compare these constructs without calling either an oracle for the other.

**TLDR-end:** [ttj: prover-target study] Learn a probability of fixed-protocol proof success with Brier loss. The executed historical test is a feasibility study, and the statement-only prospective target has separate integrity and funding requirements.
