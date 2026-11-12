# Judge migration audit and private preservation — 11-09-2026

**TLDR:** The local and latest-main audit is complete. A hash-verified private snapshot preserves experiment 110 and three criterion/transcription source notes; runtime relocation remains incomplete because analysis dependencies and historical consumers still use VeriBench paths.

This directory is ignored by Git. Do not publish raw records or source snapshots. `receipt.json` binds 23 experiment files to VeriBench main `78e1337b27a7e9469168d257457a83afd3306062` and three additional local source notes to SHA-256 hashes. All 26 copies were verified byte-for-byte. No inference, training, human collection or proof search ran.

## Repository ownership

- `judges-dont-need-psychometrics-or-corr`: general comparison of proper-loss and correlation objectives; completed matched CE/Pearson experiment 03.
- `trustworthy-theorem-judges`: applied human-rating judges, their validation and active human-rating collection.
- VeriBench: formal-prover directional formal specification coverage (FSC) and differential testing. Latest-main AGENTS.md:106 requires no LLM-rating fallback and keeps old judge-based tables historical.

## Already relocated or preserved

- Applied collection: experiment 09's public migration receipt records 1,290 preserved private files, four collection utilities and the release helper. Compatibility links remain for historical analysis consumers.
- Original handwritten notes and chat screenshot: four of four PNGs, manifest.json and USER_REQUEST.txt are identical between the original VeriBench idea folder and this project's `private/06_information_loss_vs_correlation_judge_selection/inputs/notes_11-07-2026/`.
- The two TRANSCRIPTION.md files differ. The newer VeriBench recovered-chat context is preserved here in `criterion_source_notes/notes_11-07-2026/TRANSCRIPTION.md`; neither original was overwritten.
- Completed experiment 110 is now preserved under `snapshot/experiments/110_fsc_judge_transfer_frontier_outputs_vs_human_rated_pool/`. This is a private import, not an independently runnable relocated analysis. The original remains provenance.

## Remaining units and dependencies

| VeriBench experiment or unit | Destination / action |
| --- | --- |
| ideas/leave_one_agent_out_fsc_judge_validation_on_human_ratings | Applied plan to this project; general objective notes to sister project. Preserve concurrent local edits and image provenance. |
| 100_karpathy_recipe_tc_judge_search_human_train_val_test | Applied historical import here; 45 locally modified files at audit time. |
| 106_simulated_expert_raters_icl_from_human_labels_leave_one_agent_out_fsc_judge | Applied historical import here; 51 modified files and one untracked unit, with packet consumers. |
| 110_fsc_judge_transfer_frontier_outputs_vs_human_rated_pool | Private snapshot completed here. scripts/analyze.py:22-23 still imports the VeriBench dataset and experiment 100; map those inputs before portable execution or source retirement. |
| 122_fsc_judge_gemini_vs_local_open_models_human_set | Historical measured comparison despite stale DRAFT README; keep private calls/item records private. |
| 132_gold_rewrite_swap_fsc_judge_anchoring_check; 133_alternate_gold_kernel_checked_swap_fsc_judge_anchoring_check; 134_anchoring_vs_regrade_independent_coverage_adjudication; 136_human_rerating_sample_against_alternate_gold_packet | Applied judge evidence belongs here. Preserve snapshots and receipts; experiment 136 remains prepared and unsent. |
| 75_J1_validating_formal_spec_judge_train_val_test | Split historical judge material from live prover diagnostics; 27 local modified files. |
| 102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml | Active collection already relocated; historical packet inputs and rescoring have live consumers, 123 modified files and three untracked units. |
| 117_fsc_judge_vs_prover_entailment_correlation_75_human_rated_items; 139_drop_theorem_coverage_numeric_and_tiny256_rank_check_10-31-2026; 158_gemini_lean_prover_tiny256_11-01-2026; 168_harsh_prover_pd_pf_detection_controls_tiny256_11-04-2026; 169_natural_output_prover_fsc_validation_11-06-2026 | Keep in VeriBench as prover/transition evidence; label historical model-rating comparators. |
| 140_entailment_check_vs_theorem_coverage_tiny256_10-31-2026 | Mixed historical evidence. Its README distinguishes readings from Lean-checked proofs; do not relabel all verdicts as proved. |

Concrete live consumers include `tests/test_agent_spec_and_mapping.py:383`, `paper_latex/TMLR_2026_VeriBench/make_supplementary_zip.sh:29`, and `paper_support/iclr2027/scripts/analyze_judge_validation.py:23-25` for experiment 75; `paper_support/open_weight_core614/{four_metrics_896.py,full_vs_tiny256_gap.py,saturation_per_task.py,slide5_recompute.py}` for experiment 102. Frozen records must retain their original path provenance; executable consumers need explicit updates before removal.

VeriBench latest main still has callable legacy model-rating code in `scripts/scsc/run_real_eval.py:523,578`. Version 3's scorer refuses that retired provider route at `scripts/scsc/v3/run_real_eval_v3.py:93`. Callable code does not prove current execution. The repository is not yet free of legacy LLM-judge code.

## Criterion sources and continuation

The public correction is `judges-dont-need-psychometrics-or-corr/experiments/03_exp06_ce_vs_pearson_matched_budget/EVALUATION_CRITERION_11-09-2026.md`. RPS means ranked probability score; the user clarified WE was a typo for cross-entropy (CE). The prospective human study uses individual-rating normalized RPS; experiment 03 retains its frozen CE contrast. Earlier worst-solver cumulative discrepancy and experiment 07's square-root CDF distance are distinct from raw RPS.

Next migration action: enumerate experiment 110's external input paths from its scripts and manifests, bind the required immutable inputs, and verify its deterministic analysis from the new location. Then redirect executable consumers and retire the old active entry point. Do not delete other agents' dirty work or publish private snapshots. This audit makes no new scientific claim and does not authorize collection dispatch.

**TLDR-end:** [judge migration: ownership and preservation] Criterion and dependency audit complete; private preservation verified. Collection is already relocated, while the remaining runtime migration needs its input and consumer updates.
