# Compare validation selection and training on 75 human-rated outputs

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/archive/16_compare_validation_selection_and_training_on_75_rated_outputs/README.md>

**TLDR:** ③ (rank candidate judges by validation loss, training data helps) did not beat ④ (fit by loss on all train tasks) on held-out tasks, over the same 1,000 task-grouped 20/5 splits as experiment 12: ③ by validation RPS is 0.021 worse on RPS (interval above 0) and ③ by validation CE returns the constant forecast. ② and ④ still tie on RPS. Cached judges, CPU only, $0.

Plan and rules: [PROTOCOL.md](PROTOCOL.md). Results: [results.md](results.md), [results/results.json](results/results.json). Code: [scripts/run_exp16.py](scripts/run_exp16.py), [scripts/make_report16.py](scripts/make_report16.py); shared pieces (data loader, metrics, mixture solvers) are the experiment 12 scripts copied unchanged.

Data: the experiment 12 dataset (75 artifacts, 25 tasks, 195 expert ratings, five cached judges), rebuilt by [scripts/build_dataset.py](scripts/build_dataset.py); it stays private (individual ratings), so the run needs the VeriBench private checkout. Reproduce: `python scripts/build_dataset.py` then `python scripts/run_exp16.py --data dataset.json --out results`, then `python scripts/make_report16.py results/results.json results.md`. Python 3.12.3 venv with numpy 2.5 and scipy 1.18 (versions in the results file).

Limits: five test and five validation tasks per split, a small candidate family, no new prompts or models, no agent search. See results.md.

Note on names: experiments 10 to 14 are cited by their original numbers. Experiments 11 to 14 now live in the sister repository [judges-dont-need-psychometrics-or-corr](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/tree/main/experiments/archive) (experiment 12 is `archive/12_formulation2_vs_4_corr_vs_ce_80_20_splits`); experiment 10 is [here](../10_fit_5_judge_mixtures_to_75_outputs_pearson_vs_ranked_probability/README.md).
