<!-- TLDR: Report the complete eight-artifact pilot, its conditional losses and unresolved larger validation. -->
# Fresh local prover-target judge results

Status, 11-06-2026: completed. No validated replacement or judge winner is established.

The frozen local condition produced 3/8 available target outcomes (0 successes, 3 unsuccessful bounded searches). All eight declared artifacts and four selected task families remain below. The larger frontier target and family-disjoint validation are unfinished.

| Artifact | Generation | Target | Target status | J0 probability | J1 probability |
|---|---|---:|---|---:|---:|
| T01_G0 | completed | 0 | bounded_search_unsuccessful | unavailable | 0.0000 |
| T01_G1 | completed | 0 | bounded_search_unsuccessful | unavailable | 0.0000 |
| T02_G0 | completed | missing | invalid_context | 0.0000 | 0.0000 |
| T02_G1 | completed | missing | invalid_context | 0.0000 | 0.0000 |
| T03_G0 | completed | missing | invalid_context | 0.0000 | 0.0000 |
| T03_G1 | completed | missing | invalid_context | 0.0000 | 0.0000 |
| T04_G0 | completed | 0 | bounded_search_unsuccessful | 0.0000 | 0.0000 |
| T04_G1 | completed | missing | invalid_context | 0.0000 | 0.0000 |

J0/J1 share the same pinned Qwen3.5 9B backbone; thinking is disabled for both; direct/checklist prompts have 256/1,024 output tokens. These are configuration comparisons, not model-family transfer. Only paired available cells enter conditional losses; missing cells are never encoded as zero.

| Judge | Available pairs / 8 | Conditional Brier | 95% task-family bootstrap interval | Full-denominator Brier bounds | Mean probability | Mean target | Signed bias | Descriptive MAE |
|---|---:|---:|---|---|---:|---:|---:|---:|
| J0 | 1 | 0.0000 | [0.0, 0.0] | [0.0, 0.875] | 0.0000 | 0.0000 | 0.0000 | 0.0000 |
| J1 | 3 | 0.0000 | [0.0, 0.0] | [0.0, 0.625] | 0.0000 | 0.0000 | 0.0000 | 0.0000 |

Intervals use 10,000 paired resamples of four purposively selected task families (p-val=n/a). They are descriptive and cannot establish population precision. Brier is primary; mean absolute error (MAE) is descriptive. Full-denominator bounds put every missing loss anywhere in [0,1].

Prespecified constant baselines and paired differences,  correlation availability, exact accounting and input hashes are in [analysis.json](results/analysis.json). If outcome classes or forecasts are constant, correlations and area under the receiver operating characteristic curve are unavailable.

Accounting: 38/48 reserved calls; 39,936/60,416 requested output tokens; 2,714 observed output tokens in terminal receipts; 0 calls lack terminal token counts. Provider charges: $0. Wall time: 498.2880 seconds. Raw local streams and receipts are retained privately.

The target requires both consistency and coverage proofs under the frozen bounded procedure. An unsuccessful search is semantically unresolved. Source tasks were previously exposed; newly generated outputs do not make this a fresh-family test. The four cases were selected from a source population with 14 emitted and 86 unresolved contexts out of 100. No full-benchmark score, frontier comparison, human-rating replacement or end-to-end cost-saving claim follows.

**TLDR-end:** [ttj: fresh local prover-target judges] The complete local pilot ledger and proper-loss accounting are recorded. The larger validation remains pending.
