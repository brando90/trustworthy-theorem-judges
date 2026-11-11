"""Write results.md for Experiment 14 from results/<pool>/results.json (three pools) and results/judge_table.json. No new fitting.
Usage: ~/.venvs/judge/bin/python make_report14.py   (run from the experiment folder)"""
import json
POOLS = [('old5', 'Old pool: the 5 cached frontier judges (GPT-6 Sol high, Claude Opus 5.5 max; H0/H1/H2 prompts)'),
         ('open', 'Open pool: only the open-weight judges (new, this experiment)'),
         ('all', 'Combined pool: old 5 plus open-weight judges')]
R = {k: json.load(open(f'results/{k}/results.json')) for k, _ in POOLS}
J = json.load(open('results/judge_table.json'))
f = lambda x, n=4: 'n/a' if x is None else f'{x:.{n}f}'
def pr(r, key, n=4):
    v = r['paired'][key]; return f"{v['point']:+.{n}f} [{v['ci95'][0]:+.{n}f}, {v['ci95'][1]:+.{n}f}]"
CK = 'spearman (test-set correlation, task-attributed): '; PK = 'pearson (test-set correlation, task-attributed): '
o = ['# Experiment 14 results: ② (pick by train correlation) versus ④ (pick by train cross-entropy) on a large open-weight judge pool\n']
o.append('**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/14_open_weight_judge_pool_corr_vs_ce_80_20/results.md>\n')
o.append('@@TLDR@@\n')
o.append('## ② minus ④, repeated 80/20 task splits (1,000 splits, 20 train / 5 test tasks, humans held out), with 95% task-bootstrap intervals\n')
o.append('Lower is better for RPS (main), CE and TVD, so a positive difference means ④ (CE-fit) is better. For Spearman and Pearson (higher is better) a positive difference means ② (correlation-fit) is better. "Mixture" = weights on the simplex over the pool, "single" = best single judge by the train criterion.\n')
for k, lab in POOLS:
    r = R[k]; o.append(f"### {lab} ({len(r['candidate_order'])} judges)\n")
    o.append('| Comparison | RPS (main) | CE | TVD | Spearman | Pearson |\n| --- | --- | --- | --- | --- | --- |')
    for x, y, nm in [('corr_mixture_pearson', 'ce_mixture', '② Pearson mixture minus ④ CE mixture'), ('corr_mixture_spearman', 'ce_mixture', '② Spearman mixture minus ④ CE mixture'), ('corr_single', 'ce_single', '② best single minus ④ best single')]:
        c = [pr(r, f'{mt}: {x} minus {y}', 4 if mt == 'rps' else 3) for mt in ('rps', 'ce', 'tvd')]
        c += [pr(r, f'{CK}{x} minus {y}', 3), pr(r, f'{PK}{x} minus {y}', 3)]
        o.append(f'| {nm} | ' + ' | '.join(c) + ' |')
    o.append('\nMean test score of each chooser (RPS / CE / TVD / Spearman / Pearson):\n')
    o.append('| Chooser | RPS | CE | TVD | Spearman | Pearson |\n| --- | --- | --- | --- | --- | --- |')
    L = {'constant': 'constant (train marginal)', 'equal_mixture': 'equal-weight mixture', 'corr_single': '② best single by train Pearson', 'corr_mixture_pearson': '② mixture maximizing train Pearson',
         'corr_mixture_spearman': '② mixture maximizing train Spearman (random simplex search, 4,000 draws)', 'ce_single': '④ best single by train CE', 'ce_mixture': '④ mixture minimizing train CE'}
    for m in L:
        cm = r['corr_metrics']
        o.append(f"| {L[m]} | {f(r['metrics']['rps'][m])} | {f(r['metrics']['ce'][m],3)} | {f(r['metrics']['tvd'][m],3)} | {f(cm['spearman'][m]['mean_over_splits'],3)} | {f(cm['pearson'][m]['mean_over_splits'],3)} |")
    o.append(f"\nOptimizer certificate failures: {r['optimizer_certificate_failures']}. Mean RPS of ② Pearson mixture minus equal-weight mixture: {pr(r, 'rps: corr_mixture_pearson minus equal_mixture')}; ④ CE mixture minus equal-weight: {pr(r, 'rps: ce_mixture minus equal_mixture')}; ④ minus constant: {pr(r, 'rps: ce_mixture minus constant')}.\n")
o.append('## Each judge on its own (all 75 artifacts, in-sample, no fitting)\n')
o.append('Expected rating of each judge versus the human mean rating (Pearson, Spearman) and its forecast scores against the human rating distribution. A judge is one model x one prompt, three cached or sampled ratings per artifact.\n')
o.append('| Judge | Source | RPS | CE | TVD | Spearman | Pearson | mean rating |\n| --- | --- | --- | --- | --- | --- | --- | --- |')
for j in J['judges']:
    o.append(f"| {j['name']} | {j['source']} | {f(j['rps'])} | {f(j['ce'],2)} | {f(j['tvd'],3)} | {f(j['spearman'],3)} | {f(j['pearson'],3)} | {f(j['mean_rating'],2)} |")
open('results.md', 'w').write('\n'.join(o) + '\n')
print('\n'.join(o)[:6000])
