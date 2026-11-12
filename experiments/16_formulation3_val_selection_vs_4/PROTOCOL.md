# Protocol (written before the full run; a 40-split smoke test had already run to check the code)

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/16_formulation3_val_selection_vs_4/PROTOCOL.md>

**TLDR:** ③ (choose the judge by validation loss, training data helps) versus ④ (fit by loss on train tasks only) and ② (fit by correlation), same 1,000 task-grouped 20/5 splits as experiment 12, cached judges, no model calls. Primary: ③ by validation RPS then refit on all 20 train tasks, RPS on test tasks.

- Data and test splits: exactly experiment 12 (75 artifacts, 25 tasks, five cached judges, 195 expert ratings; test seeds 20261210+s).
- Candidate judges (identical family for every method): CE-fitted mixture shrunk toward equal weights by lambda in {0, .25, .5, .75, 1}; Pearson-fitted mixture; each single judge; the train-marginal constant. Probabilities floored at 1e-6 once, as in experiments 10 to 12.
- ③: inside the 20 train tasks, 15 fit tasks and 5 validation tasks (seed 777000+s). Fit every candidate on the 15, rank on the 5 by validation loss, take the best. Primary loss RPS (the current priority plan's common validation metric); secondary loss CE (the literal formulation ③). Two readings of the winner: refit the winning candidate on all 20 train tasks (primary) or keep the 15-task fit.
- ④: the CE mixture fitted on all 20 train tasks, no validation. ②: the Pearson mixture fitted on all 20 train tasks.
- Metrics on the 5 test tasks: RPS (main), CE, TVD, then Pearson and Spearman of judge mean against human mean as secondary columns. Paired 10,000-draw task bootstrap, per-artifact values averaged over the splits where the artifact was tested.
- Nothing about the test tasks is used for any choice. Not tested: new prompts, new models, an agent search, a frontier arm.
