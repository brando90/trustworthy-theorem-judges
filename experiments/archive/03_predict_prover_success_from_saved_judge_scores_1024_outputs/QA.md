# Experiment 03: requested light review and reconciliation

**TLDR:** One Claude Fable 5.1/max subscription review reproduced the result and returned PASS with zero critical issues and two major disclosure/privacy findings; all findings are resolved below with deterministic verification.

Reviewed immutable revision: `6b288c71e09a2233e6465b6910ccfc7547e6ad8d`, against `03e4416`. The original revision and complete review remain in `research_artifacts/prover_target/review/`; their hashes are in [sources/review_receipt.json](sources/review_receipt.json). It is preserved as a private Git bundle because it contained an editable source-document locator. The original pre-analysis protocol commit `24c9152` remains in the public history. The review was not rerun.

Actual model `claude-fable-5-1` is confirmed by stream metadata; `--effort max` and `--dangerously-skip-permissions` are verified in the active process record. The provider does not separately echo effort. Authentication was verified as the existing Claude Max subscription, with provider-key variables removed. This review was implementation/research review, not measured prover or forecast inference.

| Finding | Resolution |
|---|---|
| Editable source-document locator in public metadata | Removed URL/ID from the public study, retaining private locator and public content hashes. Existing document sharing is unchanged. The unpublished reviewed commit was replaced so its locator is not left in public Git history. |
| Historical target integrity caveats understated | Added names/axioms attack results (155/212), source145 gold-proof-reuse vulnerability, hypothesis-independent proofs (51/789, two with all), and the exact scope of the 1,023-bridge scan. Natural-output semantic error remains unmeasured. |
| Constant Pearson numerical edge case | Explicit constant-vector detection, regression checks for non-binary fractions, regenerated JSON: all constant correlations are unavailable. Brier results are unchanged. |
| Coarse ridge grid | Reported that zero wins all five selections; preserved the original grid. Any finer grid is a new condition. |
| Uneven score-level accuracy | Added post hoc descriptive forecast/outcome bands, including substantial overprediction in the 0.9 band. No refit or selection used them. |
| Mean absolute error interpretation | Removed its optimization arrow and stated it is descriptive, not a proper probability score. |
| Task-family overlap | Reproduced the reviewer’s name heuristic: 28 families cross splits; 26/128 test tasks have a fitting-split sibling. No semantic-family or independent-family claim; original split retained. |
| Prior exposure and bridge-author access | Added source140 precursor cross-tabulation exposure and source142’s lack of evidence that score access was withheld from bridge authors. |
| Terminology and artifact definition | Defined artifact as one solver run on one task; named the feature a judge-produced scalar formal specification coverage (FSC) rating. |
| Funding evidence locator | Recorded exact non-secret gate file paths, SHA-256 hashes and pause/allowlist status in sources/funding_gate.json. |
| Wording and cost scope | Changed negative-improvement wording; explicitly stated that no new language-model forecast was evaluated and end-to-end cost savings were not measured. |

Reviewer checks: 17/17 source blobs matched Git and recorded hashes; source join and acceptance counts matched; separate analysis/renderer reproduction was byte-identical; task separation, training-only prevalence, ridge selection, paired bootstrap and proper-loss identities passed. Builder checks after fixes: full regeneration, strict parsing/proper-loss/constant-correlation/split tests, Python compilation, spelling and Git whitespace checks. After merging the parent’s updated main branch, `scripts/check_project.py`, the experiment 02 design validator and `scripts/build_paper.py` also passed; the paper PDF was byte-unchanged. The public history scan found no editable source-document locator. All six review-evidence hashes match, and all 83 private files were copied with SHA-256 verification to the canonical repository’s `research_artifacts/prover_target/`; `preservation_manifest.json` records the transfer. The parent owns publication and the Google companion.

**TLDR-end:** [ttj: prover-target study] The single requested independent review is complete and its findings are fixed. The reviewed statistical result is unchanged, with stronger integrity, family-overlap and cost limitations.
