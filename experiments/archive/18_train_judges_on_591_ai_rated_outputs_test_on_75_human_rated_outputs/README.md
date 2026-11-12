# Train judges on 591 AI-rated outputs and test on 75 human-rated outputs

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/archive/18_train_judges_on_591_ai_rated_outputs_test_on_75_human_rated_outputs/README.md>

**TLDR:** Fit on 591 fresh VeriBench experiment 106 artifacts labelled by AI raters, test on the 75 human-rated artifacts. Loss-fitted ④ beats correlation-fitted ② narrowly on RPS, but neither beats the untrained equal-weight mixture, and fitting on the 75 humans does better; the pool fits lean on the H0 Opus judge, the worst single config against humans. Four cached judge configs, CPU only, no model calls, $0.

Results: [results.md](results.md), [results/results.json](results/results.json). Code: [scripts/run_exp18.py](scripts/run_exp18.py), [scripts/make_report18.py](scripts/make_report18.py); shared code is imported from [experiment 16's scripts](../16_compare_validation_selection_and_training_on_75_rated_outputs/scripts). Plan: [big-training-data inventory](../../../docs/big-training-data-inventory-11-10-2026.md) (version 1 only).

Data stays private: the pool and the judge cells come from the private `veribench` checkout (experiment 106, `expt_v5/results/targets.csv`, `expt_v5/runs/*/cells.jsonl`), the human ratings from experiment 12's dataset. Reproduce: `python scripts/run_exp18.py --v106 <veribench experiment 106 dir> --human dataset.json --out results --boot 2000 --splits 1000`, then `python scripts/make_report18.py results/results.json results.md`. Python 3.12.3, numpy 2.5.4, scipy 1.18.1. The 2,000-draw bootstrap with refits took about 45 minutes on a shared 4-core machine.

Limits: four configs only, AI-rater labels (about two families per fresh item), no agent search (version 2) and no frontier arm. See results.md.

Note on names: experiments 10 to 14 are cited by their original numbers. Experiments 11 to 14 now live in the sister repository [judges-dont-need-psychometrics-or-corr](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/tree/main/experiments/archive) (experiment 12 is `archive/12_formulation2_vs_4_corr_vs_ce_80_20_splits`); experiment 10 is [here](../10_fit_5_judge_mixtures_to_75_outputs_pearson_vs_ranked_probability/README.md).
