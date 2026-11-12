<!-- TLDR: The completed local pilot did not validate a judge: malformed statements and a single observed outcome class prevent a nontrivial comparison. -->
# Fresh local prover-target judge results

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/05_fresh_local_prover_target_judges/results.md>

**Companion notes:** [Google Doc](https://docs.google.com/document/d/1zB-gYk-zU1wToS_E_carGSRGtUcF1NgZ-jWF5t1SJws)

**Status, 11-06-2026: completed local feasibility test; no validated judge or winner.** The original thinking-enabled condition failed preflight. Its separately frozen non-thinking recovery finished all declared cells, but five statements were malformed and all three available bounded-prover outcomes were 0. Every parsed judge probability was also 0. The prespecified constant-zero baseline matches both judges.

## Complete artifact ledger

There were eight generation attempts on four purposively selected, previously exposed task families, with seven unique statement/context-source hashes. Only three artifacts were well formed: two duplicate statements from one task plus one statement from another. Thus there are two unique well-formed statements on two families, not eight independent test items.

| Artifact | Statement/context | Prover outcome | J0 direct | J1 checklist |
|---|---|---:|---:|---:|
| T01_G0 | well formed | 0 | missing (token cap) | 0.0 |
| T01_G1 | well formed; duplicate of T01_G0 | 0 | missing (token cap) | 0.0 |
| T02_G0 | invalid syntax/type | missing | 0.0 | 0.0 |
| T02_G1 | invalid syntax/type | missing | 0.0 | 0.0 |
| T03_G0 | invalid syntax/type | missing | 0.0 | 0.0 |
| T03_G1 | invalid syntax/type | missing | 0.0 | 0.0 |
| T04_G0 | well formed | 0 | 0.0 | 0.0 |
| T04_G1 | invalid syntax/type | missing | 0.0 | 0.0 |

J0 and J1 are direct/checklist prompt configurations of the same Qwen3.5 9B Q4_K_M backbone, both with thinking disabled, capped at 256/1,024 output tokens. Generator prompts also share that backbone. Fourteen of sixteen forecasts parsed; the two missing J0 forecasts exhausted their frozen token limits and were not retried. Prefix-name syntax and extra nested lambdas account for the invalid contexts. They are not encoded as failed semantic implications.

## Proper loss and missingness

| Forecast | Available probability/outcome pairs | Conditional Brier | Full eight-artifact Brier bounds |
|---|---:|---:|---|
| J0 | 1/8 | 0.0000 | [0.0, 0.875] |
| J1 | 3/8 | 0.0000 | [0.0, 0.625] |
| Fixed 0.0 | 3/8 | 0.0000 | [0.0, 0.625] |
| Fixed 0.5 | 3/8 | 0.2500 | [0.09375, 0.71875] |
| Fixed 0.8 | 3/8 | 0.6400 | [0.24, 0.865] |
| Fixed 1.0 | 3/8 | 1.0000 | [0.375, 1.0] |

Conditional mean probability, mean target, signed bias and descriptive mean absolute error are all 0 for each judge, on only 1 paired artifact for J0 and 3 for J1. J0 versus J1 has only one shared available artifact. These zeros provide no evidence of useful discrimination: the outcome and forecast classes are constant, so Pearson, Spearman, Kendall and area under the receiver operating characteristic curve are unavailable. No repeated-forecast variability was measured in the recovery.

Inferential intervals are unavailable. J0 has one observed family and J1 has two. Of 10,000 bootstrap draws, J0 retains 6,843 and drops 3,157 empty draws; J1 retains 9,375 and drops 625. The frozen four-family bootstrap mechanically returns [0,0] for observed judge losses; this is a degenerate resampling result, **not a precision or population-accuracy claim**. Empty resamples and their counts are explicit in [the detailed analysis](conditions/nonthinking_v2/results/analysis.json), p-val=n/a. The displayed bounds are hypothetical completed-loss bounds: if every missing cell had a defined binary target and forecast, its loss could lie anywhere in [0,1]. These are not confidence intervals, and malformed artifacts do not acquire a defined semantic score through this calculation. Missing outcomes or forecasts are never assigned zero. This support-count qualification was added after execution; the frozen analysis script and computed losses are unchanged. Brier is primary; absolute error is descriptive. No human ratings are used or replaced.

## Target interpretation and controls

The new local condition requires independently checked proofs of both candidate consistency and implication to every exported reference obligation. Its immutable statements, separate trusted kernel replay, exact goal types and axiom filter passed four source-context replays and fifteen designed controls. All six local-model proof attempts on the three valid artifacts returned parseable proof JSON but their proof terms were rejected; the fixed tactics also failed. Therefore these outcomes are bounded-search failures. A failed search alone says nothing conclusive about semantic entailment.

The builder (Codex) wrote the proof terms after the frozen outcomes. Separate post-outcome diagnostics checked 2/2 counterexamples for the unique well-formed statements. Each certificate also supplies satisfying candidate functions, so these cases are consistent but do not imply the gold. The duplicate T01_G1 shares the exact T01_G0 statement/context hashes. These diagnostics never entered judge inputs and do not alter any operational target. See [diagnostic hashes](results/diagnostics.json).

The executed procedure also has two prompt limitations: proof terms are elaborated outside `namespace Natural`, which the judge/prover prompts did not disclose, and random temporary paths enter error feedback. Two proof attempts failed on unqualified `GoldSpec`; duplicate statements therefore did not receive byte-identical proof requests. Three adversarial controls exercise only the text filter, not kernel replay. These details and the separate reviewer checks are recorded in [post-run protocol observations](PROTOCOL_OBSERVATIONS.md); frozen protocols and outcomes are unchanged.

This is a distinct local prover condition, not VeriBench experiment169’s Pi/Gemini target. Source169 retains all 100 cases: 14 emitted contexts and 86 unresolved. This pilot selected four emitted cases for simple interfaces and makes no natural-population, frontier-model or unseen-task-family claim. The larger family-disjoint evaluation in [experiment04](../04_fresh_prover_target_judge_validation/PLAN.md) remains unfinished.

## Shared accounting and audit

Both conditions together reserved 46/56 calls and 49,152/81,920 requested output tokens, with 9,777 observed output tokens in terminal receipts. Provider charges were $0; measured execution elapsed 905.62 seconds (15.09 minutes), excluding preparation and review. Hardware use is not an end-to-end cost-saving result. No cap was reset and no failed measured cell was retried.

The first condition used eight preflight calls, with six completed responses and two output-token failures; it generated no fresh artifact. The recovery used 38 calls: eight preflight, eight generation, sixteen forecast and six proof requests. Its preflight passed all eight checks. Actual model/server identities, combined token counts and thinking-character counts are retained; the server did not expose separate thinking-token counts.

- [Shared summary](results/summary.json) and [receipt verification](results/verification.json).
- [Original failed condition](results/v1_results.md) and its unchanged [freeze](sources/freeze.json).
- [Recovery protocol](conditions/nonthinking_v2/PROTOCOL.md), [freeze](conditions/nonthinking_v2/sources/freeze.json) and [detailed report](conditions/nonthinking_v2/results.md).
- [Reproduction runbook](RUNBOOK.md). Raw inputs, statements, proof attempts, model streams and certificates remain private.

**TLDR-end:** [ttj: fresh local prover-target judges] The fresh local experiment is complete, with immutable target checks and full failure accounting. It did not identify a validated AI judge; a larger, distinct-outcome evaluation remains necessary.
