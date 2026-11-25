Independent recomputation task (QA). Read only qa_input.json in this folder. Write your own Python (numpy and scipy are fine) and run it. Do not trust any number stated anywhere; recompute.

qa_input.json: list of 175 artifacts. Fields: id, task (anonymised task id), set ("old" or "new"), split ("train", "val", "test"), ratings (list of integer human ratings 0-5), astra and opus (each a list of integer judge scores 0-5, 3 repeats old, 3 repeats new), h3_score and h3_expected (a third judge's score and expected score; present for all train/val/test artifacts), final_Q (only for test artifacts: the final judge's forecast distribution over scores 0..5).

Definitions:
- Human distribution P = empirical histogram of the artifact's ratings over 0..5. Every metric is the mean over artifacts of the subset (equal weight per artifact).
- RPS = mean over the 5 thresholds k=0..4 of (CQ_k - CP_k)^2 + CP_k*(1-CP_k), with cumulative sums CP, CQ. CE = -sum_b P_b ln Q_b (terms with P_b=0 are 0). TVD = 0.5 sum |P_b - Q_b|. Floor Q at 1e-6 and renormalise before CE.
- Constant forecast per set: Q = histogram of ALL ratings (pooled over artifacts) of the train+val artifacts of the same set, floored at 1e-6 and renormalised. Pooled constant: same over train+val of both sets. Uniform: 1/6 each. Earlier H2 judge: histogram of the 6 scores astra+opus pooled per artifact (over 0..5), floored, renormalised.

Tasks:
1. On test artifacts (70; pooled, old only, new only) compute RPS, CE, TVD for: final_Q, constant per set, pooled constant, uniform, H2 judge. Also Spearman and Pearson between each forecast's mean (sum_b b*Q_b) and the human mean rating (skip constants).
2. Paired differences final_Q minus constant-per-set and minus H2 on RPS, CE, TVD, pooled test, with 95% percentile intervals from a task bootstrap (resample whole test tasks with replacement, 10,000 draws, seed 20261124 for numpy default_rng; sample task indices with rng.integers(0, n_tasks, n_tasks) over the sorted list of unique test tasks).
3. Leakage checks: tasks must not appear in more than one split; no artifact has fewer than 1 rating; final_Q sums to 1 per artifact; list the number of artifacts and tasks per split and set.
4. Refit check: fit an ordinal cumulative-logit model P(score<=k)=sigmoid(theta_k - w.x), theta increasing, x = standardised [mean(astra), mean(opus), h3_score, h3_expected] (standardise with train+val mean and sd), by minimising the mean per-artifact CE between each artifact's human histogram P and the model distribution over train+val artifacts (no regularisation, no mixing). Predict on test and report RPS, CE, TVD pooled; compare with final_Q's numbers. Small differences from optimiser tolerance are fine.
Write results to qa_result.json and print a compact table. Report any number you are unsure about and anything that looks wrong.
