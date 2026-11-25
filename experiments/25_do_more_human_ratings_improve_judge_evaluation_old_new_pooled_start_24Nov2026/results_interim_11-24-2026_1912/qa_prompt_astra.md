You have no shell or file access in this turn: do not call any tools. Write one complete, self-contained Python 3 script (numpy only; scipy not needed) and reply with that script alone in one code block, no explanation. The script will be run by someone else on a file qa_input.json in its working directory and must write qa_result.json and print a compact table. Test mentally for correctness; it must run first time.

Task specification:
Independent recomputation task (QA). Your script reads qa_input.json only.

qa_input.json: a list of 175 artifacts. Fields: set ("old" 75 or "new" 100), id, task (anonymised task id), ratings (list of integer human ratings 0-5), astra and opus (each a list of 3 integer judge scores 0-5, one judge each).

Definitions:
- Human distribution P = empirical histogram of the artifact's ratings over 0..5 (6 bins, sums to 1).
- Judge distribution Q = histogram of the 3 judge scores over 0..5, then each bin floored at 1e-6 and renormalised to sum 1.
- RPS (per artifact) = mean over the 5 thresholds k=0..4 of (CQ_k - CP_k)^2 + CP_k*(1-CP_k), where CP, CQ are cumulative sums of P, Q.
- CE (per artifact) = -sum_b P_b * ln Q_b (terms with P_b = 0 are 0). TVD = 0.5 * sum |P_b - Q_b|.
- Every metric is the mean over artifacts (equal weight per artifact).
- Spearman and Pearson: correlation across artifacts of the judge mean score vs the human mean rating (Spearman with average ranks for ties).
- Constant baseline: for each artifact, Q = histogram of all human ratings pooled over all artifacts of OTHER tasks (leave-one-task-out) within the same set, floored at 1e-6 and renormalised; its RPS is computed against P as above. "Pooled" constant = same but computed with all other tasks of both sets together. "Set-aware" constant = the within-set one (first sentence).

Compute for each judge (astra, opus), for set old, set new, and both pooled (175): n artifacts, RPS, CE, TVD, Spearman, Pearson, constant RPS (within-set leave-one-task-out; for the pooled row give both the pooled-constant and the set-aware constant RPS). Also the 95% percentile task-bootstrap interval of RPS for set new (resample whole tasks with replacement, 2000 draws, seed 1). Also split-half check: for artifacts with >= 2 ratings, over 200 random splits of each artifact's ratings into two halves, the mean RPS between the half histograms.
Write results to qa_result.json and print a compact table. Report any number you are unsure about.

The script prints for each judge (astra, opus) and each set (old, new, pooled): n, RPS, CE, TVD, Spearman, Pearson, constant RPS (pooled row: both pooled-constant and set-aware), the new-set RPS 95% interval, and the split-half RPS; and saves all in qa_result.json.
