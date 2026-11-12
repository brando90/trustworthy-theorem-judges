"""Write results.md and learning_curve_rps.png of experiment 17 from results/results.json. Usage: python make_report17.py results/results.json . (needs matplotlib)"""
import json, sys
from pathlib import Path
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
r = json.load(open(sys.argv[1])); out = Path(sys.argv[2]); L = r['labels']; NS = r['NS']; KS = r['KS']
CT = r['curve_tasks']; CR = r['curve_ratings']; PL = r['powerlaw']
show = ['constant', 'corr_mixture_pearson', 'ce_mixture', 'equal_mixture']
col = {'constant': '#7f7f7f', 'corr_mixture_pearson': '#D55E00', 'ce_mixture': '#0072B2', 'equal_mixture': '#009E73'}
fig, ax = plt.subplots(1, 2, figsize=(10, 4), gridspec_kw={'width_ratios': [2, 1]})
for m in show:
    y = [CT['rps'][m][str(n)]['point'] for n in NS]; ax[0].plot(NS, y, marker='o', color=col[m], label=L[m].split(' (')[0])
    ax[1].plot(KS, [CR['rps'][m][str(k)]['point'] for k in KS], marker='o', color=col[m])
ax[0].set_xlabel('training tasks (nested subsets of the 20 train tasks)'); ax[0].set_ylabel('held-out RPS (lower is better)'); ax[0].legend(fontsize=7, frameon=False)
ax[1].set_xlabel('ratings per artifact in training (20 tasks)'); ax[1].set_xticks(KS, ['1', '2', 'all (2-3)'])
for a_ in ax: a_.spines[['top', 'right']].set_visible(False)
fig.suptitle('Learning curve of a learned judge on the real ratings (25 tasks, cached judges, 1,000 splits, test = 5 held-out tasks)', fontsize=9); fig.tight_layout(); fig.savefig(out/'learning_curve_rps.png', dpi=150)
f = lambda v, d=4: f"{v['point']:.{d}f} [{v['ci95'][0]:.{d}f}, {v['ci95'][1]:.{d}f}]"
fs = lambda v, d=4: f"{v['point']:+.{d}f} [{v['ci95'][0]:+.{d}f}, {v['ci95'][1]:+.{d}f}]"
o = ['# Experiment 17 results: learning curve of a learned judge on the real human ratings', '',
     '**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/17_learning_curve_tasks_and_ratings/results.md>', '',
     f"**TLDR:** Held-out RPS of the CE-fitted mixture (④) falls from {CT['rps']['ce_mixture']['4']['point']:.4f} with 4 training tasks to {CT['rps']['ce_mixture']['20']['point']:.4f} with 20 (drop {fs(r['drop_4_to_20']['ce_mixture'])}) and is nearly flat after about 12 tasks; the Pearson-fitted mixture (②) falls more slowly, from {CT['rps']['corr_mixture_pearson']['4']['point']:.4f} to {CT['rps']['corr_mixture_pearson']['20']['point']:.4f}, so ④ is ahead at small n and the gap closes by 20. Human ratings per artifact matter little at 20 tasks. Cached judges, 25 tasks, no model calls, $0.", '',
     f"Harness: no LLM in the loop; cached scalar ratings of five judges (VeriBench experiment 100, Vals Valkyrie harness, gpt-6-sol-high and claude-opus-5-5) fitted by a CPU script (Claude Code, Sonnet 5.5). {r['splits']} splits (same 20/5 task splits as experiment 12); per split one random order of the 20 train tasks, the first n are the training set, so the subsets are nested. N = number of tasks and D = ratings per artifact are my reading of the whiteboard formula l = E + A N^-alpha + B D^-beta (an open question to Brando). Task bootstrap, {r['bootstrap_draws']:,} draws.", '',
     '![learning curve](learning_curve_rps.png)', '', '## Held-out RPS against training tasks (point [95% task-bootstrap interval])', '',
     '| Training tasks | ' + ' | '.join(L[m].split(' (')[0] for m in show) + ' |', '|---|' + '---|'*len(show)]
for n in NS: o.append(f'| {n} | ' + ' | '.join(f(CT['rps'][m][str(n)]) for m in show) + ' |')
o += ['', 'The absolute intervals are wide because tasks differ a lot in difficulty; they are shared across methods, so the paired differences below are the informative ones.', '',
      '## Paired: ④ CE mixture minus ② Pearson mixture, RPS (negative = ④ better)', '', '| Training tasks | difference [95% interval] |', '|---|---|']
for n in NS: o.append(f"| {n} | {fs(r['paired_ce_minus_corr'][str(n)])} |")
o += ['', '## Drop in RPS from 4 to 20 training tasks (positive = more tasks help)', '', '| Method | drop [95% interval] |', '|---|---|']
for m in ['constant', 'corr_single', 'corr_mixture_pearson', 'ce_single', 'ce_mixture']: o.append(f"| {L[m]} | {fs(r['drop_4_to_20'][m])} |")
o += ['', '## Other metrics at 20 training tasks', '', '| Method | CE | TVD |', '|---|---|---|']
for m in ['constant', 'corr_mixture_pearson', 'ce_mixture']: o.append(f"| {L[m]} | {CT['ce'][m]['20']['point']:.3f} | {CT['tvd'][m]['20']['point']:.4f} |")
o += ['', '## Human ratings per artifact used for training (20 tasks), RPS', '', '| Ratings per artifact | ' + ' | '.join(L[m].split(' (')[0] for m in show) + ' |', '|---|' + '---|'*len(show)]
for k in KS: o.append(f"| {'1' if k == 1 else '2' if k == 2 else 'all (2 to 3)'} | " + ' | '.join(f(CR['rps'][m][str(k)]) for m in show) + ' |')
o += ['', f"CE mixture, 1 rating to all: {fs(r['drop_4_to_20']['ce_mixture, ratings 1 to all'])}; 2 ratings to all: {fs(r['drop_4_to_20']['ce_mixture, ratings 2 to all'], 5)}. Positive = more ratings help.", '',
      '## Power-law fit RPS(n) = E + A n^-alpha (exploratory)', '', '| Method | point E, A, alpha | bootstrap alpha p2.5, p50, p97.5 | bootstrap E p2.5, p50, p97.5 |', '|---|---|---|---|']
for m in ['ce_mixture', 'corr_mixture_pearson']:
    p_ = PL[m]; o.append(f"| {L[m]} | {', '.join(f'{x:.3f}' for x in p_['point_E_A_alpha'])} | {', '.join(f'{x:.2f}' for x in p_['bootstrap_alpha_p2.5_p50_p97.5'])} | {', '.join(f'{x:.3f}' for x in p_['bootstrap_E_p2.5_p50_p97.5'])} |")
o += ['', '## Plain reading', '',
      '- More training tasks help both fitted mixtures, and help the loss-fitted one fastest at first: it is already near its floor at about 12 tasks. The Pearson-fitted mixture needs more tasks to get close, so at 4 to 10 tasks ④ is clearly ahead on RPS and at 14 to 20 the interval includes 0.',
      '- With 4 training tasks the CE mixture scores the same as the equal-weight mixture (0.1496), so its gain over equal weights (about 0.013 at 20 tasks, experiment 12\'s result) only appears as tasks are added.',
      '- The curves are consistent with a power law with a floor, but the floor (E about 0.13 for ④) and exponent are fitted on 9 nested subsets of one 20-task pool, so the points are strongly dependent, the interval covers task resampling only, and the exponent is not a reliable estimate of a true scaling exponent.',
      '- At 20 tasks, 1 rating per artifact versus all 2 to 3 changes RPS by about 0.002, so within this setup the number of tasks matters more than the number of ratings per artifact.',
      '', '## What was not checked', '',
      '- Only 25 tasks exist; going past 20 training tasks, other judge families or a new judge search is not tested, so the curve says nothing about what more data would do beyond 20 tasks.',
      '- Five test tasks per split, reused across 1,000 splits: the true uncertainty is wider than the splits suggest. The cached judges\' prompts were developed with part of these ratings (see experiment 12).',
      '- N and D are guesses at the whiteboard definition; the formulation\'s B D^-beta term is not fitted separately.']
(out/'results.md').write_text('\n'.join(o)+'\n')
