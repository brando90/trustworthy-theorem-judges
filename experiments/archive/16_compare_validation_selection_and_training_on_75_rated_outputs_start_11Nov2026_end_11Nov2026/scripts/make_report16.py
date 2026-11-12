"""Write results.md of experiment 16 from results/results.json. Usage: python make_report16.py results/results.json results.md"""
import json, sys
r = json.load(open(sys.argv[1])); L = r['labels']; M = r['metrics']; P = r['paired']
meths = list(L)
def pair(mt, x, y, d=4):
    v = P[f'{mt}: {x} minus {y}']; return f"{v['point']:+.{d}f} [{v['ci95'][0]:+.{d}f}, {v['ci95'][1]:+.{d}f}]" + ('' if v['excludes_zero'] else ' (includes 0)')
def cpair(mt, x, y):
    k = f'{mt} (test-set correlation, task-attributed): {x} minus {y}'
    if k not in P: return 'not computed'
    v = P[k]; return f"{v['point']:+.3f} [{v['ci95'][0]:+.3f}, {v['ci95'][1]:+.3f}]" + ('' if v['excludes_zero'] else ' (includes 0)')
o = ['# Experiment 16 results: ③ versus ④ versus ②, 1,000 task-grouped 20/5 splits', '',
     f"**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/archive/16_compare_validation_selection_and_training_on_75_rated_outputs/results.md>", '',
     "**TLDR:** Choosing the judge by validation loss (③) did not beat fitting by loss on all 20 train tasks (④) on held-out tasks. ③ by validation RPS is worse on RPS than ④ (+0.021, interval above 0) and ③ by validation CE collapses to the constant forecast (picked in 996 of 1,000 splits). ② and ④ still tie on RPS. Retrospective, cached judges, 25 tasks, no model calls, $0.", '',
     f"Harness: no LLM in the loop; cached scalar ratings of five judges (VeriBench experiment 100, Vals Valkyrie harness, models gpt-6-sol-high and claude-opus-5-5) re-used, fitted and ranked by a CPU script (Claude Code, Sonnet 5.5 wrote and ran it). {r['splits']} splits, {r['n_artifacts']} artifacts, {r['n_tasks']} tasks, {r['bootstrap_draws']:,}-draw task bootstrap.", '',
     '## Held-out test metrics (mean over artifacts, then splits)', '', '| Method | RPS (main, lower better) | CE | TVD |', '|---|---|---|---|']
for m in meths: o.append(f"| {L[m]} | {M['rps'][m]:.4f} | {M['ce'][m]:.3f} | {M['tvd'][m]:.4f} |")
o += ['', '## Paired differences, task bootstrap 95% interval (first minus second; negative = first better for RPS, CE, TVD)', '', '| Comparison | RPS | CE | TVD |', '|---|---|---|---|']
for x, y in [('val_rps_selected_refit', 'ce_mixture'), ('val_rps_selected_fitonly', 'ce_mixture'), ('val_ce_selected_refit', 'ce_mixture'), ('val_rps_selected_refit', 'corr_mixture_pearson'), ('ce_mixture', 'corr_mixture_pearson'), ('ce_mixture', 'equal_mixture'), ('ce_mixture', 'constant')]:
    o.append(f"| {L[x]} minus {L[y]} | {pair('rps', x, y)} | {pair('ce', x, y, 3)} | {pair('tvd', x, y)} |")
o += ['', '## Secondary columns: correlation of judge mean with human mean on the test tasks (task-attributed split values; positive = first higher)', '', '| Comparison | Pearson | Spearman |', '|---|---|---|']
for x, y in [('val_rps_selected_refit', 'ce_mixture'), ('val_ce_selected_refit', 'ce_mixture'), ('val_rps_selected_refit', 'corr_mixture_pearson'), ('ce_mixture', 'corr_mixture_pearson')]:
    o.append(f"| {L[x]} minus {L[y]} | {cpair('pearson', x, y)} | {cpair('spearman', x, y)} |")
o += ['', 'Mean test-set correlation over splits (undefined when the forecast is constant): ' + '; '.join(f"{L[m]}: Pearson {r['corr_metrics']['pearson'][m]['mean_over_splits']:.3f}" if r['corr_metrics']['pearson'][m]['mean_over_splits'] is not None else f"{L[m]}: undefined" for m in meths) + '.',
      '', '## What ③ picked', '', 'Winner counts over the 1,000 validation rankings: by validation RPS ' + ', '.join(f"{k} {v}" for k, v in sorted(r['selection_counts']['rps'].items(), key=lambda kv: -kv[1])) + '. By validation CE ' + ', '.join(f"{k} {v}" for k, v in sorted(r['selection_counts']['ce'].items(), key=lambda kv: -kv[1])) + '.',
      '', '## Plain reading', '',
      '- Validation selection does not help here. With 15 fit and 5 validation tasks the ranking of candidates is noisy, and the candidates differ little, so the pick probably often lands on a worse one (single judge or constant) than the plain 20-task CE fit (an explanation I did not test).',
      '- Validation CE is dominated by the judges\' near-zero probabilities on some ratings (CE of any mixture is about 5.4 against 1.85 for the constant), so ③ by CE returns the constant almost always, which has the worst RPS and undefined correlations.',
      '- ② (Pearson mixture) and ④ (CE mixture) remain a tie on RPS (-0.006 [-0.018, +0.006]); ④ wins CE and ② wins the correlation columns, as in experiment 12.',
      '', '## What was not checked', '',
      '- Five test tasks and five validation tasks per split is tiny; the 1,000 splits reuse the same 25 tasks, so the intervals come from the task bootstrap only and the true uncertainty is wider than the number of splits suggests.',
      '- The candidate family is small (five cached judges, mixtures). No new prompts, no agent search and no model calls, so this does not test ③ as a prompt or model search. The cached judges\' prompts were developed with the original train split of these ratings, so held-out tasks may have been seen at design time.',
      '- Validation RPS as the ③ loss follows the current priority plan; the literal CE version is shown as the second ③ row. Folds are grouped by task, not by task family or rater.',
      '- The primary reading ("refit on all 20") and the secondary reading ("keep the 15-task fit") were both declared in PROTOCOL.md before the full run and both are shown.']
open(sys.argv[2], 'w').write('\n'.join(o)+'\n')
