"""Write results.md from results/results.json and results/fixed_split_agents.json (no new fitting).
Usage: ~/.venvs/judge/bin/python make_report.py"""
import json, numpy as np
R = json.load(open('results/results.json')); A = json.load(open('results/fixed_split_agents.json')); fx = R['fixed_split']
L = {'constant': 'constant (train marginal)', 'equal_mixture': 'equal-weight mixture', 'corr_single': '② best single judge by train Pearson',
     'corr_mixture_pearson': '② mixture maximizing train Pearson', 'corr_mixture_spearman': '② mixture maximizing train Spearman',
     'ce_single': '④ best single judge by train CE', 'ce_mixture': '④ mixture minimizing train CE'}
f = lambda x, n=4: 'n/a' if x is None else f'{x:.{n}f}'
o = []
o.append('# Experiment 12 results: ② (pick by correlation) versus ④ (pick by cross-entropy), 80/20 task splits\n')
o.append('**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/12_formulation2_vs_4_corr_vs_ce_80_20_splits/results.md>\n')
P = R['paired']; g = lambda k: P[k]
def pr(k, n=4): v = g(k); return f"{v['point']:+.{n}f} [{v['ci95'][0]:+.{n}f}, {v['ci95'][1]:+.{n}f}]"
o.append(f"**TLDR:** On {R['splits']} random 20-train/5-test task splits of the 75 cached artifacts, ② (mixture of the five cached judges chosen to maximize train Pearson) and ④ (mixture chosen to minimize train cross-entropy) tie on the main metric RPS: ② minus ④ = {pr('rps: corr_mixture_pearson minus ce_mixture')} (lower is better, so no evidence either way). ④ is better on CE ({pr('ce: corr_mixture_pearson minus ce_mixture',3)}, ② worse), ② is better on the correlations with the human mean rating (Spearman {pr('spearman (test-set correlation, task-attributed): corr_mixture_pearson minus ce_mixture',3)}). Retrospective on cached judge scores, 0 model calls, $0, CPU only.\n")
o.append('Method: each split holds out 5 whole tasks (15 artifacts); every method is fitted on the other 20 tasks (60 artifacts) only. ② = judge that maximizes the Pearson (or Spearman) correlation between its expected rating and the human mean rating; ④ = judge that minimizes cross-entropy to the human rating distribution. The searched family is the same for both: a single cached judge, or a weighted mixture of the five cached judges (weights on the simplex). Test metrics per artifact are averaged over the splits where the artifact was held out, then a 10,000-draw task bootstrap (25 tasks) gives the 95% percentile interval of the paired difference. Correlations need several test artifacts, so each split\'s test-set correlation is attributed to its 5 test tasks and averaged per task before the same bootstrap. Lower is better for RPS, CE, TVD; higher for correlations.\n')
o.append(f"## Repeated splits ({R['splits']}), mean test score\n")
o.append('| Method | RPS (main) | CE | TVD | Spearman (mean over splits) | Pearson (mean over splits) |\n| --- | --- | --- | --- | --- | --- |')
for m in L:
    o.append(f"| {L[m]} | {f(R['metrics']['rps'][m])} | {f(R['metrics']['ce'][m],3)} | {f(R['metrics']['tvd'][m],3)} | {f(R['corr_metrics']['spearman'][m]['mean_over_splits'],3)} | {f(R['corr_metrics']['pearson'][m]['mean_over_splits'],3)} |")
o.append('\nThe constant has no spread, so its correlations are undefined.\n')
o.append('## Paired differences, ② minus ④ (95% task-bootstrap interval)\n')
o.append('| ② variant versus ④ variant | RPS | CE | TVD | Spearman | Pearson |\n| --- | --- | --- | --- | --- | --- |')
for x, y, lab in [('corr_mixture_pearson', 'ce_mixture', '② Pearson mixture vs ④ CE mixture'), ('corr_mixture_spearman', 'ce_mixture', '② Spearman mixture vs ④ CE mixture'), ('corr_single', 'ce_single', '② best single judge vs ④ best single judge')]:
    cells = [pr(f'{mt}: {x} minus {y}', 3 if mt != 'rps' else 4) for mt in ['rps', 'ce', 'tvd']] + [pr(f'{mt} (test-set correlation, task-attributed): {x} minus {y}', 3) for mt in ['spearman', 'pearson']]
    o.append(f'| {lab} | ' + ' | '.join(cells) + ' |')
o.append('\nAgainst the plain baselines (② Pearson mixture, ④ CE mixture), paired difference on RPS:\n')
o.append('| | versus constant | versus equal-weight mixture |\n| --- | --- | --- |')
for x, lab in [('corr_mixture_pearson', '② Pearson mixture'), ('ce_mixture', '④ CE mixture')]:
    o.append(f"| {lab} | {pr(f'rps: {x} minus constant')} | {pr(f'rps: {x} minus equal_mixture')} |")
o.append(f"\nMean fitted weights (H0 Sol, H0 Opus, H1 Sol, H2 Sol, H2 Opus): ② Pearson mixture {', '.join(f'{w:.3f}' for w in R['mean_weights']['corr_mixture_pearson'])}; ④ CE mixture {', '.join(f'{w:.3f}' for w in R['mean_weights']['ce_mixture'])}. Best single judge chosen: ② H2 Opus in {R['single_judge_choice_counts']['corr_single']['H2_opus']} of {R['splits']} splits; ④ H2 Opus {R['single_judge_choice_counts']['ce_single']['H2_opus']}, H0 Sol {R['single_judge_choice_counts']['ce_single']['H0_sol']}, H2 Sol {R['single_judge_choice_counts']['ce_single']['H2_sol']}. Each artifact was a test artifact in {R['test_count_per_artifact_min_max'][0]} to {R['test_count_per_artifact_min_max'][1]} splits. Optimizer certificate failures: {R['optimizer_certificate_failures']}.\n")
o.append('## One fixed split (seed 1210, declared before fitting), 20 train / 5 test tasks\n')
o.append(f"Test tasks: {', '.join(fx['test_tasks'])} (15 artifacts). Five tasks is very small: these are single numbers, not evidence.\n")
o.append('| Chooser | Judge chosen | RPS | CE | TVD | Spearman | Pearson |\n| --- | --- | --- | --- | --- | --- | --- |')
for m in ['corr_mixture_pearson', 'ce_mixture', 'corr_single', 'ce_single', 'constant', 'equal_mixture']:
    t = fx['test'][m]; w = fx['weights'][m]
    ws = 'constant' if w is None else ' '.join(f'{n}:{v:.2f}' for n, v in zip(R['candidate_order'], w) if v > 0.005)
    o.append(f"| optimizer: {L[m]} | {ws} | {f(t['rps'])} | {f(t['ce'],3)} | {f(t['tvd'],3)} | {f(t['spearman'],3)} | {f(t['pearson'],3)} |")
for nm, lab in [('corr', 'Claude Code agent, correlation objective only'), ('ce', 'Claude Code agent, CE objective only')]:
    a = A['agents'][nm]; t = a['test']; ws = ' '.join(f'{n}:{v:.2f}' for n, v in a['weights'].items() if v > 0.005)
    o.append(f"| {lab} | {ws} | {f(t['rps'])} | {f(t['ce'],3)} | {f(t['tvd'],3)} | {f(t['spearman'],3)} | {f(t['pearson'],3)} |")
d = np.array([A['agents']['corr']['per_task'][k]['rps'] - A['agents']['ce']['per_task'][k]['rps'] for k in fx['test_tasks']])
rng = np.random.default_rng(7); bs = [d[rng.integers(0, 5, 5)].mean() for _ in range(10000)]
o.append(f"\nAgent ② minus agent ④ on RPS, per test task: {', '.join(f'{k} {v:+.4f}' for k, v in zip(fx['test_tasks'], d))}; mean {d.mean():+.4f}, 5-task bootstrap interval [{np.percentile(bs,2.5):+.4f}, {np.percentile(bs,97.5):+.4f}] (illustration only).\n")
o.append('The agents searched a slightly larger family than the repeated-split optimizers: the five judges plus the constant train marginal as a sixth component. Pearson is unchanged by adding a constant, so the marginal weight in ② is arbitrary (the agent said so); for ④ the marginal weight is what fixes calibration, which is why the agent-④ CE on the fixed split is much lower than the optimizer-④ CE.\n')
o.append('## What the metrics are (per artifact; p = human rating distribution from the 2 to 3 expert ratings, q = the judge\'s output distribution over the six ratings 0 to 5)\n')
o.append('- RPS (ranked probability score, main): mean over the five cumulative cut points of (Q_k - P_k)^2 + P_k(1 - P_k), with P, Q the cumulative sums of p and q. Proper for ordinal ratings, sensitive to how far off the mass is, and it never blows up. Lower is better.')
o.append('- CE (cross-entropy): -sum_r p(r) log q(r), with q floored at 1e-6. Proper but unbounded: a judge that puts almost no mass on a human-given rating pays a lot. Lower is better.')
o.append('- TVD (total variation distance): half the sum of |p(r) - q(r)|, the largest probability difference between the two distributions, 0 to 1. Lower is better.')
o.append('- Spearman and Pearson (secondary): rank and linear correlation, over the 15 test artifacts of a split, between the judge\'s expected rating and the human mean rating. They only check the means, not the whole distribution. Higher is better.\n')
o.append('## Harness and models\n')
o.append('- Optimizing agent: a Claude Code subagent started by the Claude Code worker (Sonnet 5.5 is the worker; the subagent model was not recorded separately), one for ② and one for ④, each given only the 60 training artifacts of the fixed split and one objective, using a 0.05-grid search over the simplex in plain Python (the second also an EM optimizer). They did not see the 5 test tasks. Both made 0 model calls.')
o.append('- Repeated splits: no LLM in the loop. The selection is the exact solver of experiment 10/03 (Pearson mixture by active-face enumeration, CE mixture by SLSQP with a checked certificate), a 4,000-point simplex search for Spearman, and argmax or argmin over single judges. Orchestrated by the Claude Code worker.')
o.append('- Judges: the five cached judges, produced earlier (VeriBench experiment 100, commit be287d9): GPT-6 Sol high and Claude Opus 5.5 max with the H0, H1, H2 prompt variants. Nothing new was called.')
o.append('- Cost $0 (cached scores, CPU).\n')
o.append('## Limits and what was not checked\n')
o.append('- Small: 25 tasks, 75 artifacts (three Claude 3.7 Sonnet samples per task), 2 to 3 expert ratings per artifact (195 in total), not about five raters. A split tests on only 5 tasks.')
o.append('- Prior exposure and leakage risk: the five judges\' prompts and conventions were developed in experiment 100 using the original train split\'s human ratings (10 of the 25 tasks, and some prompts also saw validation tasks). In these random splits some held-out tasks were therefore seen when the judges were designed, which can flatter every method alike; a clean test needs new rated tasks. These ratings were also inspected in experiments 06, 07, 10 and 11.')
o.append('- No new prompts or models were searched: "choose the best prompt or model" here means choosing among five cached prompt-and-model judges and their mixtures. A search over new prompts or local open-weight judges needs model calls and was not run.')
o.append('- Folds are grouped by task, not by task family, so family leakage is possible. Splits overlap, so the 1,000 splits are not independent; the intervals come from bootstrapping the 25 tasks.')
o.append('- Test-set correlations use 15 artifacts per split and are task-attributed (see Method); they are not the pooled correlation over all 75 artifacts.')
o.append('- The cached judges\' CE is poor because three cached samples put near-zero mass on many human-rated values; ② does not try to repair calibration, so a CE gap against ④ is expected by construction.')
open('results.md', 'w').write('\n'.join(o) + '\n'); print('\n'.join(o))
