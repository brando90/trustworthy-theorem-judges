"""TLDR: Render the verified frozen results without fitting or selecting any model."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
r = json.loads((ROOT/'results/results.json').read_text())
t = json.loads((ROOT/'results/terminal.json').read_text())
v = json.loads((ROOT/'results/verification.json').read_text())
bv = json.loads((ROOT/'results/verification_refit_samples.json').read_text())
assert t['status'] == 'COMPLETE' and v['status'] == bv['status'] == 'PASS'
names = {'mixture_weighted_pmf':'Weighted mixture', 'mixture_pearson':'Pearson mixture',
         'softmax_weighted_pmf':'Weighted softmax', 'softmax_ce':'Cross-entropy softmax',
         'softmax_brier':'Brier softmax', 'softmax_rps':'Ranked-score softmax',
         'constant':'Training-marginal constant'}
labels = {'weighted_pmf':'Weighted squared PMF loss', 'ce':'Cross-entropy',
          'kl':'Forward Kullback–Leibler divergence', 'brier':'Brier loss',
          'rps':'Normalized ranked probability score', 'tvd':'Total variation distance',
          'pearson':'Pearson r', 'spearman':'Spearman rho', 'kendall':'Kendall tau',
          'mae':'Mean absolute error', 'bias':'Mean bias (judge minus human)',
          'human_mean':'Human mean', 'judge_mean':'Judge mean', 'entropy':'Human empirical entropy'}
metrics = list(labels)
ci = lambda d: f"{d['estimate']:+.6f} [{d['lo']:+.6f}, {d['hi']:+.6f}]"
lines = ['<!-- TLDR: Weighted mixture training has lower observed held-out weighted loss than stable Pearson training, but the paired interval includes zero; softmax differences are also unresolved. -->',
'# Weighted training results — 11-08-2026', '',
'**Status: COMPLETE, independently verified.** Weighted squared probability mass function (PMF) training reduced observed held-out weighted loss from **0.202068 to 0.191659**, but the paired difference was **−0.010409 [−0.061911, +0.005933]** (95% task-family bootstrap interval with both mixtures refitted; 998/1,000 valid draws; p-val=n/a). This historical sample does **not resolve an advantage** over stable Pearson training. All 50 primary fits passed their optimality checks, and all 900 secondary softmax fits converged.', '',
'**Collaborator message:** “I tested weighted probability training against a stable correlation baseline on the same family-held-out artifacts. The weighted mixture looks better on several distribution scores, but the uncertainty still includes no improvement, so I would treat this as exploratory evidence rather than a demonstrated win.”', '',
'**Experiment:** `06_information_loss_vs_correlation_judge_selection/training_followup_11-08-2026`. All rows below belong to this condition. [Protocol](PROTOCOL.md) · [Configuration](protocol.json) · [Mathematical baseline](MATH_baseline.md) · [Raw aggregate results](results/results.json) · [Verification](results/verification.json) · [Resample verification](results/verification_refit_samples.json) · [Checkpoint](CKPT_training_followup.md).', '',
'## What was tested', '',
'Both primary methods fit one global nonnegative mixture of the same five cached judge histograms, with weights summing to one. Weighted training minimizes the human-frequency-weighted squared PMF distance; Pearson training globally maximizes correlation between expected ratings. The predictions, folds and held-out metric panel are identical. The numerical baseline replaces the earlier unstable comparison with a separately frozen condition; it does not repair or relabel the old softmax Pearson fits.', '',
'A secondary experiment fits the same six-category affine softmax family under weighted loss, cross-entropy, Brier loss and ranked probability score. Four inner family folds choose regularization by ranked probability score for every method. Comparing a softmax result with a mixture result changes the model class as well as the objective, so that comparison cannot isolate the objective.', '',
'Data: 75 artifacts, 25 tasks, 19 task families, 195 human ratings, five cached judges with three scalar ratings per artifact. Each of five fixed partitions has five outer task-family folds. Every method produces 375 held-out forecast rows across the five overlapping partitions; this is still 75 distinct artifacts, not 375 independent observations. Means and absolute errors use rating/5; log losses use natural logarithms. Cached model/rubric provenance remains in [the source audit](../source_audit.json).', '',
'## Primary matched mixture comparison', '',
'Each point estimate averages the five pooled out-of-fold results. The last column is weighted minus Pearson, with the 95% family-bootstrap interval **including mixture refitting**. Lower losses/errors are better; higher correlations are better; a bias closer to zero is better. No hypothesis test was prespecified (p-val=n/a).', '',
'| Held-out metric | Weighted mixture | Pearson mixture | Paired difference [95% interval] |',
'|---|---:|---:|---:|']
for metric in metrics:
    lines.append(f"| {labels[metric]} | {r['matrix']['mixture_weighted_pmf'][metric]:.6f} | {r['matrix']['mixture_pearson'][metric]:.6f} | {ci(r['mixture_refit_differences'][metric])} |")
lines += ['',
'Weighted training had lower observed weighted distance, cross-entropy, Brier loss, ranked probability score and total variation. It also had higher observed held-out Pearson correlation, while Pearson training had higher Spearman and Kendall correlations. Every paired interval for these contrasts includes zero. Absolute agreement also has no resolved advantage: mean absolute errors are 0.156471 and 0.156112, respectively. Both methods rate higher than the human mean (0.525333): weighted mean 0.576704, bias +0.051370; Pearson mean 0.588829, bias +0.063496.', '',
'Training behaved as intended: the unweighted average over the 25 training folds gives weighted loss 0.184840 for weighted fitting versus 0.209614 for Pearson fitting, and training Pearson 0.775709 versus 0.808762. These training summaries are diagnostics, not held-out evidence. Globally optimizing training correlation did not guarantee the highest held-out correlation.', '',
'## Secondary softmax comparison', '',
'All four methods use the same probability family, features, initialization convention, optimizer limits, regularization grid and validation score. Each has 225 fits, including 25 final outer-training refits. All 900 fits converged; iteration counts ranged from 16 to 151. The table is descriptive; paired uncertainty follows.', '',
'| Training objective | Weighted PMF loss | Cross-entropy | Brier | Ranked probability score | Pearson |',
'|---|---:|---:|---:|---:|---:|']
for method in ['softmax_weighted_pmf','softmax_ce','softmax_brier','softmax_rps','constant']:
    lines.append('| '+names[method]+' | '+' | '.join(f"{r['matrix'][method][k]:.6f}" for k in ['weighted_pmf','ce','brier','rps','pearson'])+' |')
lines += ['',
'Weighted softmax has the lowest observed weighted PMF loss of these four fitted objectives, but none of its weighted-loss contrasts resolves an advantage. Brier training has the lowest observed cross-entropy, Brier and ranked probability scores in this condition; this does not establish a general winner. The constant is fitted independently in each outer training fold, so its pooled out-of-fold expected ratings vary and its pooled correlation can be negative even though it is constant within a fold.', '',
'| Weighted softmax minus | Weighted PMF difference [95% interval] | Cross-entropy difference [95% interval] | Ranked-score difference [95% interval] |',
'|---|---:|---:|---:|']
for loss in ['ce','brier','rps']:
    d=r['conditional_differences']['softmax_weighted_minus_'+loss]
    lines.append('| '+names['softmax_'+loss]+' | '+' | '.join(ci(d[k]) for k in ['weighted_pmf','ce','rps'])+' |')
lines += ['',
'These secondary intervals use 1,000 paired task-family resamples of the **fixed fitted predictions**; they exclude fitting and regularization-selection uncertainty. They must not be presented as full-procedure intervals. All draws were valid; p-val=n/a.', '',
'## Verification, failures and uncertainty limits', '',
f"The full manifest completed in {t['elapsed_seconds']:.3f} seconds on one CPU thread on skampere3: 50 mixture fits, 900 softmax fits, 100 regularization choices, 175 final models and 2,625 forecast rows including the constant. Independent verification reconstructed every final forecast, checked all 900 training-only transformations, reproduced all 100 validation choices, checked all 50 mixture certificates and recomputed all 14 aggregate metrics. Source and result hashes match the frozen launch revision `{t['source_commit']}`. Python {r['python']}, NumPy {r['numpy']}, SciPy {r['scipy']}.", '',
'The earlier preflight summary listed different installed package versions; the run receipt above is authoritative. See [environment clarification](ENVIRONMENT_NOTE.md). Both control suites passed inside the actual scientific process before empirical fitting. No scientific settings or results were changed.', '',
'The 1,000 paired family-bootstrap draws attempted 49,049 mixture fits. Empty test folds need no fits. Two draws failed the frozen 1e-8 certificate gate and remain invalid: draw 192 failed the weighted simplex gap (1.38010e-7); draw 562 failed the Pearson cone certificate (4.34071e-8). No tolerance was relaxed and no draw was replaced. The reported refit intervals condition on the 998 successful draws, so they have this numerical missingness limitation. No training correlation was undefined. Independent replay reproduced both failures and draws 0, 499 and 999; the largest metric discrepancy was 3.33e-16. The replay validates existing evidence and creates no new resampling draws.', '',
'These are exploratory results on previously inspected historical ratings and a fixed candidate pool, not a fresh sealed test. Resampling covers task-family sampling and mixture-weight refitting conditional on the fixed partitions and cached ratings. It does not cover upstream judge/prompt selection, repeated human sampling, new solvers or new rater populations. Two or three human ratings per artifact give sparse empirical histograms; three sampled scalar model ratings are not native probability forecasts of human uncertainty. Standard deviations over five overlapping repartitions quantify split sensitivity, not five independent experiments.', '',
'Weighted squared PMF distance here is mean_i sum_r p_ir (p_ir − q_ir)^2. It is an empirical distribution distance, not the single-observation loss (1 − q_R)^2 and not a claim that this weighting is a proper scoring rule for a new individual rating. Brier and ranked probability scores average their ordinary categorical/ordinal scoring rules over available human ratings.', '',
'No new inference calls were made; provider inference charges were $0. Subscription coordination usage was not measured. Individual ratings, forecasts, fitted weights and resampling arrays are retained in ignored canonical private storage; public evidence contains aggregates only.', '',
'## Which ideas remain untested', '',
'This phase completes weighted-PMF numerical training and a stable, matched Pearson baseline. Earlier conditions already tested fixed-candidate selection with correlation, cross-entropy, weighted PMF, Brier, ranked probability score, total variation, Wasserstein and Gaussian-kernel distance. The earlier softmax experiments and this phase are fitted mappings of cached ratings.', '',
'Still untested here: direct language-model or agent-prompt optimization under these objectives; native six-category probability forecasts; a fresh sealed human-rating comparison; transfer to unseen solvers and raters; direct stable Spearman/Kendall training; Wasserstein/Gaussian-kernel training; and softmax uncertainty that refits the full training/validation procedure. The focused literature check also remains a focused check, not a systematic frontier-wide survey. These require separately specified conditions; no claim of their completion follows from this run.', '',
'## Full common metric panel and variability', '',
'Every row below shows the point estimate, a 95% family-bootstrap interval conditional on fixed predictions, and the standard deviation (SD) across the five overlapping repartitions. These per-method intervals differ from the primary paired **refit** intervals above. Each method has 1,000 valid conditional draws. All metrics and full paired contrasts are also machine-readable in results/results.json.', '']
for method in r['methods']:
    lines += [f"### {names[method]}", '', '| Metric | Estimate [conditional 95% interval] | Repartition SD (5) |','|---|---:|---:|']
    for metric in metrics:
        d=r['conditional_intervals'][method][metric]
        lines.append(f"| {labels[metric]} | {r['matrix'][method][metric]:.6f} [{d['lo']:.6f}, {d['hi']:.6f}] | {r['resplit_standard_deviations'][method][metric]:.6f} |")
    lines.append('')
lines += ['**TLDR-end:** [ttj: weighted training] The requested historical-data comparison is complete. Weighted mixture training improved observed distribution losses, but its paired uncertainty does not establish superiority over stable correlation training.', '']
(ROOT/'RESULTS_training.md').write_text('\n'.join(lines))
print('Rendered RESULTS_training.md from verified aggregate evidence.')
