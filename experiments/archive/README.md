# Archived experiments

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/archive/README.md>

**TLDR:** Completed or superseded experiment records live here. Archive means historical, not invalid or deleted. Current work and important live references are listed in the [experiment index](../README.md).

## Relocation record — 11-11-2026

All paths below are relative to the repository root. Each destination is under `experiments/archive/`; original experiment numbers are retained. Every tracked file inside these archived folders was moved without changing its bytes, including protocols, scripts, results, source manifests and historical READMEs.

| Previous home | Archived home | Reason and outcome | Preserved tracked files |
| --- | --- | --- | ---: |
| `experiments/01_legacy_veribench_judge/` | [01_legacy_veribench_judge](01_legacy_veribench_judge/README.md) | Historical scalar-judge evidence; source receipts remain available to the paper and project checks. | 10 |
| `experiments/03_prover_target_fsc_judge/` | [03_prover_target_fsc_judge](03_prover_target_fsc_judge/README.md) | Retrospective prover-outcome analysis complete; prospective follow-up belongs to experiment 04. | 17 |
| `experiments/05_fresh_local_prover_target_judges/` | [05_fresh_local_prover_target_judges](05_fresh_local_prover_target_judges/README.md) | Local feasibility condition complete; no judge validated; broader validation remains in experiment 04. | 55 |
| `experiments/06_information_loss_vs_correlation_judge_selection/` | [06_information_loss_vs_correlation_judge_selection](06_information_loss_vs_correlation_judge_selection/README.md) | Cached objective comparisons complete; ongoing objective research moved to the sister repository. | 83 |
| `experiments/11_formulation4_train_only_ce_mixture_cv/` | [11_formulation4_train_only_ce_mixture_cv](11_formulation4_train_only_ce_mixture_cv/README.md) | Train-only cross-entropy mixture study complete; retrospective evidence, no new model calls. | 14 |
| `experiments/12_formulation2_vs_4_corr_vs_ce_80_20_splits/` | [12_formulation2_vs_4_corr_vs_ce_80_20_splits](12_formulation2_vs_4_corr_vs_ce_80_20_splits/README.md) | Correlation-versus-cross-entropy split comparison complete; retrospective evidence. | 26 |
| `experiments/13_toy_pearson_vs_ce_nonlinear_ratings/` | [13_toy_pearson_vs_ce_nonlinear_ratings](13_toy_pearson_vs_ce_nonlinear_ratings/README.md) | Nonlinear synthetic-rating comparison complete; conclusions are limited to the toy construction. | 13 |
| `experiments/14_open_weight_judge_pool_corr_vs_ce_80_20/` | [14_open_weight_judge_pool_corr_vs_ce_80_20](14_open_weight_judge_pool_corr_vs_ce_80_20/README.md) | Open-weight judge-pool comparison complete; retrospective evidence with mixed objective comparisons. | 59 |

The T, A, H planning bundle moved separately from `experiments/02_probabilistic_ordinal_judge/rating_tensor_planning/` to [experiment 15](../15_rating_tensor_size_estimation/README.md). Its source exports and original attachments retain identical bytes; editable navigation, source index and attribution of the optional Codex pilot proposal were updated. The bundle's current hashes are in [provenance.json](../15_rating_tensor_size_estimation/provenance.json).

## Reading and reproducing historical work

Archived documents and frozen configurations retain the paths recorded when the work ran. Use the destination table above for current navigation. An old path in a recorded result or quoted chat is provenance, not a second active copy. Private stores, sealed ratings and delivered packets have not moved.

The complete pre-relocation layout is available at [commit 15f150d](https://github.com/brando90/trustworthy-theorem-judges/tree/15f150d8a2797a655d0937c7b7fcc37135aa2628). For exact historical reproduction, restore that revision in an isolated temporary checkout and follow that experiment's frozen protocol and private-data requirements. In particular, experiments 03 and 05 derive repository/private paths from their original directory depth; their frozen scripts are preserved here and must be replayed in the original layout, not launched directly from the archive. Moving a script does not authorize inference or lift an existing funding gate.

Current consumers were repaired: the project verifier reads archived experiment 01; experiment 04 resolves experiment 03's recorded input paths into this archive while leaving its frozen configuration unchanged; experiment 07 imports the preserved experiment 06 data importer here. Current documentation and Google companion navigation point to the relocated homes. Historical source bodies and immutable commit URLs remain unchanged.

Experiments 02 (current methodology), 04 (paused fresh study), 07 (current metric/sample-size reference), 08 (pending review and follow-up), 09 (active collection) and 15 (current sizing question) retain their numbered homes. Experiment 10 remains in place because its owner's detached publication worktree contains a unique, unlanded checkpoint addition. The worktree at `~/.worktrees/trustworthy-theorem-judges/paper-publication-receipt-11-10-2026` is preserved for the sole collection coordinator; archive 10 after that publication receipt is reconciled and landed. No running analysis was inferred from the presence of the worktree.

## Relocation checks

Compared all 277 archived tracked files against the pre-relocation commit: every file is byte-identical. Also verified the six experiment-15 source exports/attachments, its current public hash inventory, 104 current local links and passage anchors, the unchanged phase-0 configuration and relocated input hashes, and experiment 07’s importer entry point. The project verifier (33 tests plus design/source/style checks) and paper build passed. The paper-source edit only updates a provenance comment; rebuild-only PDF changes were discarded.
