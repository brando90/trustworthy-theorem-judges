<!-- TLDR: The existing prover records support operational acceptance analysis, but their bridge faithfulness, proof dependence and historical search budgets limit semantic conclusions. -->
# Located implementation and evidence

All private VeriBench sources were read from committed revision `be287d9bb2f7bd35ba6db1b8735c9ba10d00eade`, not its shared working tree. Exact paths, byte counts and SHA-256 hashes are in [sources/provenance.json](sources/provenance.json). Restricted source snapshots remain in ignored `private/prover_target/source/`; only aggregate evidence and source metadata are exported here.

## Experiment 117: abstract-function proof search

`117_fsc_judge_vs_prover_entailment_correlation_75_human_rated_items/expt_v1/scripts/VB117Harness.lean` constructs universally quantified functions and candidate-statement hypotheses. `decideGoal` builds the exact implication, tries a tactic sweep and generated proof text, then calls `kernelAccept` and `axiomsOk`. It also searches for countermodels. Results distinguish proved, refuted, unknown, unstatable and agent-independent goals. This is theorem-level fractional coverage, not one all-obligation bit per artifact.

Its committed tier-T2 protocol pins Goedel-Prover-V2-8B revision `dfd02e6271a58375dfbf3ece0175277cf6b6a89a` and DeepSeek-Prover-V2-7B revision `a8d9e14432b2e8dd9df2a4d4e70f1ba9bc8d9b7b`, 32 samples each, seed 1, temperature 1, top-p 0.95, maximum 16,384 new tokens, context 32,768, vLLM 0.21.0 and at most six graphics-processor hours. The recorded gate remained 10/30 decided statable, agent-dependent train goals, below its 0.50 continuation threshold. Its failed gate stays failed; this study does not resume it or quote a nonexistent judge correlation.

## Experiment 140: binary readings

`140_entailment_check_vs_theorem_coverage_tiny256_10-31-2026/PROTOCOL.md` asks readers whether all public gold statements follow from an arbitrary candidate function satisfying its stated specifications, through a “natural” adapter. Proof completion is not part of that reading. `LEAN_PROTOCOL.md` later asks for Lean proofs/countermodels on disagreements. The original `entails` values are readings, not uniformly kernel-checked certificates. This study uses only the manifest’s preexisting scalar `tc` as a predictor feature, not the binary reader opinions as truth.

## Experiments 142 and 145: historical binary acceptance

`142_entailment_lean_proofs_all_tiny256_10-31-2026/README.md` describes bridge authoring across 1,024 historical Tiny256 artifacts, one prover per two artifacts, with at most two compile-repair rounds. The prover is identified as helper agents of the same assistant; the exact model/version/effort is not established by that protocol. The search budget was not a uniform fixed token/wall-time budget. Thus the archived binary response can be predicted, but it is not a reproducible modern prover condition without additional provenance.

`145_entailment_vacuity_axiom_check_tiny256_11-01-2026/results/per_run.csv` records the final `counted_all5` target. Gates require accepted entailment, allowed axioms in both the entailment proof and every named candidate theorem, an unchanged gold file, a witness of candidate assumptions, and a proved counterpart for every public gold name. This removes 39 raw successes for candidate theorem axioms and 12 additional successes for missing gold names. These are gate outcomes, not observed semantic failures.

The implementation matters:

- `lean/GoldChkLib.lean` enumerates public named gold declarations, finds `Bridge.G_*` declarations, checks theorem status and collects transitive axioms. It does not compare the bridge theorem type with the transported gold theorem type. Matching names and allowed axioms are insufficient to bind the intended proposition.
- `lean/WitLib.lean` instantiates bridge hypotheses using candidate definitions and standard-axiom candidate theorems. This is evidence of consistency of those hypotheses, conditional on faithful extraction. It does not alone establish that a precondition inside every implication is satisfiable.
- `lean/AxLib.lean` checks named candidate theorems. Consequently the historical acceptance flag depends on original proof status/axioms, whereas the requested formal specification target concerns statements. The source’s own caveat says faithfulness of transported statements and semantic adapters remains a reading.
- A valid Lean proof of a wrong bridge proposition can pass these mechanical checks. The source explicitly says its five conditions do not prevent gold-proof reuse: a prior seven-attack control set had six raw acceptances and three after name/axiom gates. Among 789 counted natural artifacts, a text heuristic marks 51 with at least one gold theorem proved without candidate hypotheses (two with all); 732 are classified as trivial or identical by a reading. These are diagnostics, not independently established semantic errors. Therefore the saved flag is not used as an unconditional semantic lower bound here.

## Experiment 168: checker integrity controls

`168_harsh_prover_pd_pf_detection_controls_tiny256_11-04-2026/attacks/summary.json` and `scripts/attacks_check_candidate_patched.py` document related fixed-goal checker controls. The source reports eight accepted forged-audit attacks among 72 tested invalid submissions for the unmodified fixed-goal checker, and zero after a nonce-bound audit patch on the same attack set. The closer analogue to the historical target, the names-and-axioms gate, accepted 155/212 constructed invalid bridge submissions (0.731, source-reported Wilson 95% interval [0.668, 0.786], p-val=n/a). Its class counts include gold-proof reuse 10/11, assuming the gold statement as an adapter hypothesis 11/11, tautology restatement 11/11, shadowed gold names 11/11 and a disjunction with True 7/7. These constructed-case counts are not error-rate estimates on natural outputs. The source explicitly identifies the parsed-audit weakness as applicable to experiment 145 too. Its text scan found no audit-line strings or printing commands in 1,023 saved bridges; candidate solver files were not scanned. The nonce patch was tested on the same attack set and does not establish closure of every attack class.

The patched checker fixes the goal imported from `Clean_*`, parses only a proof term through `ProofOnly`, and uses an audit nonce generated after the candidate proof is fixed. The general prospective requirement is trusted binding of input, exact goal, proof and environment-level axiom data; free-text compiler output alone is not a trust boundary.

`scripts/prover_pi_runner.py` belongs to experiment 168. Its named Koyejo-lab key exception and spending caps explicitly exclude other experiments. This study does not copy that exception. Live local Valkyrie pause files still allow only the previously named construction experiments.

## Additional provenance and open questions

The authoritative human-study Google Doc (locator retained privately) was fetched with the Google Drive connector on 11-06-2026; its exact returned text and retrieval metadata are protected in `private/prover_target/human_plan_drive.json`. The exported text omits some rendered equations, so the existing byte-exact supplied plan remains necessary for those formulas. This study changes the response variable, rather than silently altering that human-study plan.

Named paths searched for exact historical model settings: source 140 README, protocol, manifest; source 142 README; source 145 README and per-run receipts; source 137 README and table provenance. Those sources identify the four historical solver configurations but do not bind an exact judge model to each `tc` value or an exact authoring model/effort to each proof. Such settings are unavailable for this reanalysis; no contemporary model identity is inferred. A new measured run must resolve every scientific pin and its payer before admission.

**TLDR-end:** [ttj: prover-target study] The archived acceptance flags are reusable operational outcomes with exact source hashes. Their proof-dependent gates and unverified statement transport require a separate condition for a faithful statement-only study.

Funding evidence: the exact live paths and file hashes read on 11-06-2026 are recorded in `sources/funding_gate.json`; no secret file was read. The review confirmed anyone-with-link editing on the supplied human-plan document, so its locator remains private and its content hashes remain public. Existing sharing was not changed.
