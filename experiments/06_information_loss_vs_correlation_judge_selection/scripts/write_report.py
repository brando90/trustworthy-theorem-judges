"""TLDR: Render the complete measured comparison from aggregate execution receipts."""
import collections, json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
r=json.loads((ROOT/'results/results.json').read_text());h=json.loads((ROOT/'results/head_results.json').read_text());p=r['primary']
diagnostic=json.loads((ROOT/'results/head_verification.json').read_text())['posthoc_fit_diagnostics']
labels={'ce':'CE / forward KL','brier':'Brier','rps':'RPS','pearson':'Pearson','spearman':'Spearman','kendall':'Kendall','weighted_pmf':'Weighted PMF','tvd':'TVD'}
def table(matrix, keys, intervals=None):
    out=['| Objective | '+' | '.join(keys)+' |','| --- | '+' | '.join(['---:']*len(keys))+' |']
    for obj,vals in matrix.items():
        def entry(k):
            s=f'{vals[k]:.3f}'
            if intervals is not None:
                ci=intervals[obj][k];s+=f" [{ci['lo']:.3f}, {ci['hi']:.3f}]"
            return s
        out.append('| '+labels[obj]+' | '+' | '.join(entry(k) for k in keys)+' |')
    return '\n'.join(out)

d=p['primary_selection_refit_interval'];hd=h['ce_minus_pearson']['ce'];cd=p['ce_minus_spearman']['ce']
lines=[f'''# Cached objective comparison: results and limitations

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/06_information_loss_vs_correlation_judge_selection/RESULTS.md>

**TLDR:** The cached histogram comparison did not establish that cross-entropy selection improves held-out performance. A separate fitted probability-head comparison favored proper-loss models over the specified Pearson implementation, but that implementation usually failed to converge; general superiority remains unestablished.

Experiment `06_information_loss_vs_correlation_judge_selection`, completed 11-06-2026 (America/Los_Angeles).
Historical sample: **75 artifacts, 25 tasks, 19 task families, 195 expert ratings, five cached judges with three scores per artifact (1,125 historical calls)**.
Five seeded five-fold partitions reuse these same artifacts; they are not 375 independent artifacts.
All eight selection objectives completed all 25 outer folds (200 selections), followed by all 900 declared probability-head fits.
There were zero new model calls and $0 new provider inference charges.
The bounded CPU analyses took about 17 and 10 seconds on skampere3, excluding preparation, transfer, subscription coordination and hardware costs.

## Answer to the hypothesis

1. **Primary, fixed cached histograms:** held-out cross-entropy (CE; natural-log units, lower better) was {p['matrix']['ce']['ce']:.3f} for CE selection versus {p['matrix']['spearman']['ce']:.3f} for Spearman selection. Difference **{d['estimate']:+.3f} [{d['lo']:.3f}, {d['hi']:.3f}], p-val=n/a**. This 95% interval resamples task families and reruns candidate selection within the fixed partitions. It includes zero, so this experiment does not resolve the direction of the selection effect.
2. **Secondary, fitted probability heads:** CE fitting versus Pearson fitting gave CE {h['matrix']['ce']['ce']:.3f} versus {h['matrix']['pearson']['ce']:.3f}; difference **{hd['estimate']:+.3f} [{hd['lo']:.3f}, {hd['hi']:.3f}], p-val=n/a**. This interval is conditional on the fitted heads and excludes fitting/regularization-selection uncertainty. **215/225 Pearson fits did not converge, including 24/25 outer refits; all 675 proper-loss fits converged.** The comparison describes these bounded implementations, not fully optimized objective optima. Brier fitting had lower observed CE ({h['matrix']['brier']['ce']:.3f}) than CE fitting ({h['matrix']['ce']['ce']:.3f}); that difference was not the primary contrast.
3. **Practical conclusion:** use proper probability losses when the target is a rating distribution, but do not claim that CE/KL must improve every test metric. Three sampled scalar ratings are particularly weak probability forecasts. Fresh human data, a stable matched optimization comparator and identified probability outputs are needed before a general or deployment claim.

The primary protocol was frozen in `ea9d63b` before measurement. The head follow-up was frozen separately in `aba79e9`, after the histogram result, as the planned secondary fitting condition. It does not replace the primary outcome. No confirmatory test or success threshold was specified; all p-values are n/a.

## Primary common held-out metric matrix

The rows change only the selection objective over the same five candidates. CE and forward Kullback–Leibler divergence (KL) are one equivalent selection objective. Brier uses the six-category sum convention [0,2]; ranked probability score (RPS) averages five ordinal thresholds [0,1]. Pearson, Spearman and Kendall compare expected rating to human mean; higher is better. Other losses are lower better.

The following 95% intervals use **1,000 paired task-family bootstrap draws conditional on the already selected forecasts**, averaging each metric across the five seeded partitions. They exclude selection/fitting variability and new human/model samples. Their narrower intervals must not replace the selection-refit interval above.
''',table(p['matrix'],['ce','brier','rps'],p['conditional_intervals']), '\n'+table(p['matrix'],['pearson','spearman','kendall'],p['conditional_intervals']),
'''\nRemaining common metrics are point estimates; their conditional intervals and all paired differences are in `results/results.json`. PMF means probability mass function; TVD means total variation distance. Weighted PMF distance is sum p_hat(r)(p_hat(r)-q(r))²; TVD is half the absolute PMF difference. Human entropy is subtracted for forward KL, with identical weighting. Sparse empirical human frequencies are noisy targets for these distances.\n''',
table(p['matrix'],['kl','weighted_pmf','tvd','mae','bias','judge_mean','human_mean']),
f'''\nMean absolute error (MAE), mean bias and means use the [0,1] rating scale. Bias is judge minus human; positive means higher/lenient ratings. Spearman selection: judge mean {p['matrix']['spearman']['judge_mean']:.3f}, human mean {p['matrix']['spearman']['human_mean']:.3f}, bias {p['matrix']['spearman']['bias']:+.3f}.

For comparison, the conditional primary difference is {cd['estimate']:+.3f} [{cd['lo']:.3f}, {cd['hi']:.3f}], while repeating candidate selection yields {d['estimate']:+.3f} [{d['lo']:.3f}, {d['hi']:.3f}]. This change of interval is why fixed-prediction uncertainty alone would be misleading for the selection question. All 1,000 selection-refit draws were valid; no replacement retries occurred.

## Selected candidates and sparse support

Historical identities: H0 uses the human-mirror rubric; H1 adds rater conventions; H2 adds conventions and leave-task-out expert demonstrations. Sol is the saved `openai/gpt-6-sol-high` gateway selector at high effort; Opus is `anthropic/claude-opus-5-5-no-fallback`, compute effort max. Full saved configurations and input hashes are in `source_audit.json`; no new provider identity claim is inferred from these aliases.

| Selection objective | Candidate counts across 25 outer selections |
| --- | --- |''']
for o in p['matrix']:
    counts=collections.Counter(s['candidate'] for s in p['selections'] if s['objective']==o)
    lines.append('| '+labels[o]+' | '+', '.join(f'{k}: {v}' for k,v in sorted(counts.items()))+' |')
lines+=['''
Pearson, Spearman and Kendall chose H2 Opus in all 25 selections and therefore have identical results here. Undefined-correlation selection fallbacks: 0.

| Cached candidate | Artifacts with observed human rating outside raw forecast support /75 | Mean unsupported human mass | RMS within-artifact sample SD of three raw normalized scores |
| --- | ---: | ---: | ---: |''']
for name,v in p['zero_mass_before_smoothing'].items():
    lines.append(f"| {name} | {v['artifacts']} | {v['mean_human_mass']:.3f} | {r['repeat_variability'][name]['raw_repeat_rms_sample_sd_0_1']:.3f} |")
baseline={k:sum(v[k] for v in r['training_marginal_baseline_per_seed'])/5 for k in ['ce','brier','rps']}
lines += [f'''
Without the epsilon mixture, those unsupported observations have infinite log loss. With epsilon=1e-6, they receive about 13.816 loss each. The train-only constant human-distribution baseline had CE {baseline['ce']:.3f}, Brier {baseline['brier']:.3f}, RPS {baseline['rps']:.3f} (descriptive point estimates). All eight histogram-based selection procedures are much worse in CE than this baseline; high ranking correlation does not make their sampled-score histograms adequate human-rating distributions. The repeated-score standard deviations above concern raw calls, not the repeatability of the three-call aggregate; there is only one cached three-call batch per artifact.

## Prespecified sensitivities

All preserve the declared selection recipe. Intervals were not computed for these secondary checks.

| Condition | Artifacts / tasks / families / expert ratings | CE-selected CE | Spearman-selected CE | Difference |
| --- | --- | ---: | ---: | ---: |''']
for name,v in r['sensitivities'].items():
    ce=v['matrix']['ce']['ce'];sp=v['matrix']['spearman']['ce']
    lines.append(f"| {name} | {v['artifacts']} / {v['tasks']} / {v['families']} / {v['expert_ratings']} | {ce:.3f} | {sp:.3f} | {ce-sp:+.3f} |")
v=r['original_split'];lines.append(f"| Historical validation selection / old test | 30 test artifacts / 10 tasks / 78 expert ratings | {v['ce']['metrics']['ce']:.3f} | {v['spearman']['metrics']['ce']:.3f} | {v['ce']['metrics']['ce']-v['spearman']['metrics']['ce']:+.3f} |")
lines += ['''
`ordinary` removes 15 placeholder-reference artifacts; `ordinary_unambiguous` also removes the 15 ambiguous-reference artifacts. These are predeclared sensitivities, not a replacement dataset. Original-split selection uses only its 15 validation artifacts; its test split was previously exposed and is not fresh.

## Separate matched probability-head comparison

All conditions use the five cached mean scores as features and the same six-class affine softmax model, 36 stored coefficients, training-only feature scaling, initialization schedule, optimizer and fitting budget. Four inner family folds select between two L2 strengths by the same held-out RPS rule, independently for every fit objective. No LLM is fine-tuned; these are fitted probability mappings. See `HEAD_PROTOCOL.md`.

These 95% intervals are conditional on the fitted heads and regularization choices. They resample 19 families with all attached artifacts/ratings, 1,000 draws, and do not account for upstream prompt exposure or model-fitting uncertainty.
''',table(h['matrix'],['ce','brier','rps'],h['conditional_intervals']), '\n'+table(h['matrix'],['pearson','spearman','kendall'],h['conditional_intervals']), '\n'+table(h['matrix'],['kl','weighted_pmf','tvd','mae','bias','judge_mean','human_mean']),
'''
| Fitting objective | Fits | Nonconverged fits | Nonconverged final refits /25 | Mean train Pearson | Mean within-fold test Pearson | Mean within-fold test expected-rating SD |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |''']
for k,v in diagnostic.items():lines.append(f"| {labels[k]} | {v['fit_count']} | {v['nonconverged']} | {v['nonconverged_outer']} | {v['train_pearson']:.3f} | {v['test_pearson']:.3f} | {v['test_expected_rating_sd']:.3f} |")
lines+=['''
The fit diagnostics were added after observing the convergence failures; they do not change the frozen analysis. Pearson's mean training correlation is high, while its expected ratings have a small within-fold spread. Correlation does not identify an absolute location or scale; pooling differently fitted folds can therefore give much lower correlation than averaging within-fold correlations. The table documents that behavior without claiming it is the only cause of failure. The equal numerical regularization grid also has different effective strengths under differently scaled losses. All finite failed fits were retained, and no objective received extra retries. A stable comparator and independent data are necessary before claiming general training-objective superiority.

## Human reference and evidence limits

Descriptive leave-one-expert-out agreement on overlapping artifacts (same historical sample, no population ceiling claim):

| Anonymous expert index | Artifacts | Pearson | Spearman | Kendall | MAE |
| --- | ---: | ---: | ---: | ---: | ---: |''']
for v in r['human_leave_one_expert_out_descriptive']:lines.append(f"| {v['expert_index']} | {v['artifacts']} | {v['pearson']:.3f} | {v['spearman']:.3f} | {v['kendall']:.3f} | {v['mae']:.3f} |")
lines+=['''
- These old ratings, test outcomes, and candidate prompts had prior exposure. New family folds do not undo upstream selection or demonstration exposure. This is retrospective evidence, not an independent validation round.
- The importer matched all 75 candidate hashes to the annotation revision, all 12 input manifest hashes, and 1,125 receipt prompt hashes to their run manifests. Original rater-time delivery bytes were not independently reconstructed; reference ambiguity remains explicit. A manifest match does not eliminate these historical limitations.
- The study has one historical solver-output population and three expert columns with missingness (75/75/45 artifacts). There is no held-out solver-family or rater-family transfer test, nor evidence over all benchmark tasks.
- Both human frequencies (two or three ratings per artifact) and judge histograms (three calls) are noisy. This study does not establish closeness to the full conditional human rating distribution or all its moments.
- Proper-score theory identifies population targets under its assumptions; finite samples, model class, optimization and regularization determine the empirical result. No novelty or universal-superiority claim follows from this run.

## Reproduction and verification

See `protocol.json`, `PROTOCOL_FROZEN.md`, `HEAD_PROTOCOL.md`, `head_protocol.json`, `source_audit.json` and `scripts/`.
Private data remain in the canonical repository's ignored `private/06_information_loss_vs_correlation_judge_selection/`; no individual ratings or learned weights are published.
Run `run_cached.py` with the recorded private dataset/configuration, then `fit_heads.py` against the same root; the remote supervisors show exact argument and resource conventions.
Source/data hashes and process exit codes are in `results/terminal.json` and `results/head_terminal.json`.

Verification passed seven scoring/splitting tests, four analytic-gradient finite-difference checks (all below 1e-5), the two-example fit, independent reconstruction of 3,000 primary plus 1,500 head forecasts, 100 training-only preprocessing checks, full manifest counts and bootstrap interval recomputation. Project checks and the unchanged workshop-paper build passed. The paper's prospective claims were not replaced by retrospective results.

All aggregate matrices, per-seed metrics, selections, fit convergence records, paired intervals and sensitivity outputs are in `results/results.json` and `results/head_results.json`. Independent verification receipts are beside them. The experiment remains active as the home for the planned fresh-human confirmation; the cached conditions are complete.

Copy-ready message: I compared probability-loss and correlation-based selection using our historical human ratings. The cached selection result did not resolve an advantage for cross-entropy; fitted proper-loss probability models looked more useful, but the Pearson optimization comparator mostly failed to converge, so we still need a stable comparison and fresh ratings.

**TLDR-end:** [ttj: objective comparison] Both cached-data comparisons finished and were independently checked. They support better probability modeling and a fresh study, not a general claim that CE/KL beats correlation-based objectives.
''']
(ROOT/'RESULTS.md').write_text('\n'.join(lines))
print('Wrote RESULTS.md from measured receipts.')
