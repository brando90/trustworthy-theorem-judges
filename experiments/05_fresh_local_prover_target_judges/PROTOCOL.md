<!-- TLDR: A capped local feasibility condition tests fresh specification outputs and two identified judge configurations without replacing the blocked frontier protocol. -->
# Prospective local feasibility protocol

Status, 11-06-2026: four source contexts and 15 integrity controls passed; freezing before the first model call. This protocol is distinct from experiment04's future 64-task evaluation and VeriBench experiment169's Pi/Gemini condition. Their owners, manifests, budgets, failures and watches are unchanged.

## Question and scope

Can an end-to-end statement-only pipeline produce checked bounded-prover outcomes and explicit probability forecasts on newly generated formal specifications? This pilot tests the pipeline and describes forecast error. Four purposively selected task families cannot establish a validated replacement, a frontier comparison or population-wide accuracy. Task selection favored two-function interfaces whose pinned source169 contexts round-trip exactly, have no representation adapter and have standard-axiom source witnesses. Source169 still has 14 emitted and 86 unresolved among all 100 pairs. This study does not inherit a 14-only denominator or call those outputs fresh.

There are four source tasks, two statement-generator configurations per task, eight fresh artifacts, two judge configurations, one primary forecast per artifact/judge, and three forecasts on each of two preselected artifacts (T01/G0 and T03/G1). Thus T=4, A=2, J=2, primary K=1, repeat K=3 on two artifacts, and R=1 bounded prover search per fresh artifact. The two generator configurations and two judge configurations share one local backbone; they are not independent model families.

The source families are string length, prefix filtering, URI permission and same-origin comparison. Their Python and gold are pinned source snapshots associated with source169, not a new full-release solver run. The generator receives only Python plus the declared public two-function interface (functional and imperative versions), and returns a Lean proposition about those abstract functions. It does not implement or prove a program. Internal/reference implementation scores are unmeasured and inapplicable to this restricted statement-authoring task. All eight initial cells stay in the ledger, including malformed statements, transport failure and unfinished cells.

## New local target

`P_local_qwen9_v1` is a new condition, not experiment169's Gemini/Pi target. The immutable goal is `∀ f0 f1, CandidateSpec f0 f1 → GoldSpec f0 f1`, where GoldSpec is the conjunction of every exported reference obligation, plus a separate `∃ f0 f1, CandidateSpec f0 f1` consistency goal. The functions are arbitrary, and no concrete implementation or source proof is available. Candidate proof bodies are irrelevant by construction: the target depends only on the emitted proposition. Fresh candidate consistency must be checked anew; the old source witness does not establish it.

For each goal, try the fixed tactic battery, then at most one local-model proof term if the battery fails. There are no repair or retry calls. The event is 1 only if BOTH proofs pass independent strict kernel replay, exact goal-type equality, no newly added axioms and the allowed transitive axiom set `{propext, Classical.choice, Quot.sound}`. A completed unsuccessful search is operational 0 and semantically unresolved. Model wall-time or output-token exhaustion, invalid returned proof text, and Lean proof-search/replay timeouts consume the bounded search and yield 0 when neither attempt succeeds; service, transport, process-death or trusted-context build failures remain missing. An infrastructure failure is recorded separately with target missing. A malformed candidate has no well-formed implication and is recorded as invalid, not semantic non-entailment. Independent checked counterexamples and consistency/refutation certificates are separate diagnostics; they never enter judge inputs.

The checker reads a candidate module as data and re-adds its constants through Lean's kernel in a trusted process whose module path excludes that candidate. The reference, parser and replay modules are hash-protected. The trusted replay implementation is pinned to VeriBench ec1f9b2a4455549ba98a4fdf94c9d30bf3a0522d. Lean is 4.22.0; the installed Mathlib revision and manifest hash are recorded before execution. Proof-language filters supplement kernel checks. No credit relies on a free-form compiler log alone.

## Integrity predictions before execution

| Control | Expected observation |
|---|---|
| Source re-extraction | Four exact context hashes, round-trip equality and all reference names preserved |
| True implication plus consistency witness | Both accepted |
| Weak True specification | Counterexample checked; invented implication rejected |
| Inconsistent specification | Implication can be proved, witness rejected, inconsistency checked; combined event 0 |
| Wrong goal, unused added axiom, placeholder, native oracle, forged audit | Rejected |
| Same statement with changed candidate proof metadata | Identical target hash |
| Oracle forecast / half forecast / complemented outcome | Brier 0 / 0.25 / 1 |
| Probability reproduction controls | Exact supplied 0.25 and 0.75 reproduced; failure stops new admissions |

## Models, freezing and bounded execution

All model roles use installed `qwen3.5:9b-q4_K_M`, digest `56671c2ab9385f9cfcb404638e32cd62d88e3501d44822208363c010179a3c90`, Ollama 0.40.8 on loopback, cloud disabled, no tools or internet. Thinking is explicitly false/true for G0/G1 and J0/J1; the prover uses true. Generator output limits are 1,024/2,048 tokens for G0/G1, judge limits are 256/2,048 for J0/J1, and prover limits are 2,048; thinking consumes that same output budget. The JSON configuration fixes prompts, temperature, seeds, token limits and parsing. Neither a provider key nor a personal model subscription funds these measured calls. Provider inference cost is $0; hardware time is measured, not claimed free of resource cost.

Hard limits: 56 total reserved calls, 81,920 generated tokens by summed request limits, 180 seconds per model call, 60 seconds per Lean attempt, and four hours for the admitted local execution including finalization. Counts comprise 8 preflight calls, 8 generator calls, 24 forecasts and at most 16 prover calls. No automatic retries, fallback model or budget reset. Input context is capped at 8,192 tokens; requests record prompt hashes, actual model, completion reason, token counts and timing. Interrupted requests stay consumed and are not replayed.

Freeze code/configuration and all cell identities before any model call. Freeze every judge prompt before generating target outcomes. Run all primary and repeat forecasts before target proof search; judge inputs contain Python, candidate statements, gold statements and the exact target protocol, without proofs, certificates, outcome bits or informative historical identifiers. Fresh outputs mean new statement artifacts and new judge responses; source tasks were previously exposed in experiment03. No fitted judge or score mapping is reused, and no task-family-held-out claim relative to experiment03 is made. There is no training or validation fit in this pilot, hence no selection on test outcomes and no claimed transfer to an unseen solver family.

## Analysis and decision

Primary descriptive measure: artifact-equal Brier loss on well-formed completed target cells, with every excluded/invalid/missing cell also listed. Compare fixed forecasts 0.5, 0.8 and 1.0; these are prespecified, not fitted to test outcomes. Report denominator, success prevalence, mean forecast, signed bias, mean absolute error, pairwise Brier difference, repeat variability and parsing/transport failures. Any interval resamples the four task families with paired configurations; it is descriptive and very imprecise, p-val=n/a. Do not treat eight artifacts as eight independent tasks.

The expected positive result is a working checked pipeline with fresh probability outputs. The expected uncertainty is substantial: a small local model may fail Lean syntax/proofs, and the bounded target can fail on genuinely covering statements. A nontrivial forecast-agreement interpretation additionally needs both observed outcome classes and independently checked cases; otherwise report the degenerate result without a winner. No threshold from this pilot licenses deployment. The larger family-disjoint evaluation remains the separate experiment04 plan, with its exact prover/funding gates unresolved.

One requested Claude Fable 5.1/max subscription review covers the final new code, condition, controls and results. Fix findings and run deterministic verification; do not start another independent review round.

**TLDR-end:** [ttj: fresh local prover-target judges] Execute a bounded, independently checked local feasibility pilot on eight new specification artifacts. Preserve the separate frontier target, exposure limits and unfinished larger validation.
