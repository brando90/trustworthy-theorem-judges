# Learning curve of a learned judge on the real human ratings

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/17_learning_curve_tasks_and_ratings/README.md>

**TLDR:** Held-out RPS against the number of training tasks (4 to 20, nested) and against the number of human ratings per artifact, for the CE-fitted mixture (④), the Pearson-fitted mixture (②) and baselines. ④ is ahead at small task counts and nearly flat after about 12 tasks; ② catches up by 20; ratings per artifact matter little. Cached judges, 25 tasks, CPU only, $0.

Results: [results.md](results.md) (with [learning_curve_rps.png](learning_curve_rps.png)), [results/results.json](results/results.json). Code: [scripts/run_exp17.py](scripts/run_exp17.py), [scripts/make_report17.py](scripts/make_report17.py); it imports the shared code from [experiment 16's scripts](../16_formulation3_val_selection_vs_4/scripts). Data: the experiment 12 dataset (private; rebuilt by experiment 16's build_dataset.py).

Limits: 25 tasks only, so nothing past 20 training tasks; nested subsets of one pool make the curve points dependent; N = tasks and D = ratings is a guess at the whiteboard definition. See results.md.

Note on names: experiments 10 to 14 are cited by their original numbers. Experiments 11 to 14 now live in the sister repository [judges-dont-need-psychometrics-or-corr](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/tree/main/experiments/archive) (experiment 12 is `archive/12_formulation2_vs_4_corr_vs_ce_80_20_splits`); experiment 10 is [here](../10_fit_5_judge_mixtures_to_75_outputs_pearson_vs_ranked_probability/README.md).
