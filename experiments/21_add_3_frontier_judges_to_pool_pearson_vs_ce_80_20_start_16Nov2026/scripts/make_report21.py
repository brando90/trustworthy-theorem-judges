"""Write results.md from results/{old5,new3,all8}/results.json, results/extras21.json and results/fixed_split_agents_all8.json (no new fitting).
Usage: ~/.venvs/judge/bin/python make_report21.py   (run from the experiment folder's scripts/ or code/ with ../results present)"""
import json, os
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'results')
ld = lambda p: json.load(open(os.path.join(D, p)))
R = {p: ld(f'results_{p}.json') for p in ('old5', 'new3', 'all8')}
X = ld('extras21.json'); A = ld('fixed_split_agents_all8.json')
L = {'constant': 'constant (train marginal)', 'equal_mixture': 'equal-weight mixture', 'corr_single': '② best single judge by train Pearson',
     'corr_mixture_pearson': '② mixture maximizing train Pearson', 'corr_mixture_spearman': '② mixture maximizing train Spearman',
     'ce_single': '④ best single judge by train CE', 'ce_mixture': '④ mixture minimizing train CE'}
POOL = {'old5': 'old 5 judges (GPT-6 Sol H0/H1/H2, Opus 5.5 H0/H2) — repeat of exp 12', 'new3': 'new 3 frontier judges only (Astra, Sol 6.1, Argon)', 'all8': 'all 8 judges'}
f = lambda x, n=4: 'n/a' if x is None else f'{x:.{n}f}'
def pr(P, k, n=4):
    v = P[k]; return f"{v['point']:+.{n}f} [{v['ci95'][0]:+.{n}f}, {v['ci95'][1]:+.{n}f}]"
SP = 'spearman (test-set correlation, task-attributed): corr_mixture_pearson minus ce_mixture'
PE = 'pearson (test-set correlation, task-attributed): corr_mixture_pearson minus ce_mixture'
o = []
o.append('# Experiment 21 results: ② (pick by correlation) versus ④ (pick by cross-entropy) with a larger pool of frontier judges\n')
o.append('**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/21_add_3_frontier_judges_to_pool_pearson_vs_ce_80_20_start_16Nov2026/results.md>\n')
P = R['all8']['paired']
o.append(f"**TLDR:** Three new frontier judges (gpt-6-astra, gpt-6.1-sol, gemini-4-argon) each scored the 75 artifacts 3 times (675 calls, about $20.2 at list prices; no Opus API route worked, so no new Opus judge). With all 8 judges in the pool, ② and ④ still tie on the main metric RPS over {R['all8']['splits']} task splits: ② minus ④ = {pr(P,'rps: corr_mixture_pearson minus ce_mixture')} (lower is better). ④ is better on CE ({pr(P,'ce: corr_mixture_pearson minus ce_mixture',3)}) and TVD ({pr(P,'tvd: corr_mixture_pearson minus ce_mixture')}); ② is better on Spearman ({pr(P,SP,3)}) and Pearson ({pr(P,PE,3)}). With gpt-6-astra as the optimizing agent on one fixed split, RPS ties again, ④ is better on CE, and ② has the higher test correlations (TVD interval includes zero; 5 test tasks only).\n")
o.append("Method: identical to experiment 12 (80/20 task splits, 20 train tasks = 60 artifacts, 5 test tasks = 15 artifacts, 1,000 repeats from seed 20261210, 10,000-draw paired task bootstrap, a fixed split with seed 1210). A judge's distribution is the histogram of its 3 calls on the frozen H2 prompt, smoothed at 1e-6. ② maximizes the train Pearson (or Spearman) between the expected rating and the human mean; ④ minimizes train cross-entropy. Both search single judges and mixtures. Lower is better for RPS (main), CE and TVD; higher for Spearman and Pearson (secondary). Correlations need several test artifacts, so each split's test correlation is attributed to its 5 test tasks and averaged per task before the bootstrap. The human ratings are private and are not in this repository; `scripts/` reproduces everything given the private data.\n")
for p in ('old5', 'new3', 'all8'):
    r = R[p]
    o.append(f"## Pool: {POOL[p]}\n")
    o.append('Mean test score over the splits:\n')
    o.append('| Method | RPS (main) | CE | TVD | Spearman | Pearson |\n| --- | --- | --- | --- | --- | --- |')
    for m in L:
        c = r['corr_metrics']
        o.append(f"| {L[m]} | {f(r['metrics']['rps'][m])} | {f(r['metrics']['ce'][m],3)} | {f(r['metrics']['tvd'][m])} | {f(c['spearman'][m]['mean_over_splits'],3)} | {f(c['pearson'][m]['mean_over_splits'],3)} |")
    o.append('\n② minus ④ (paired 10,000-draw task bootstrap, 95% interval):\n')
    o.append('| Comparison | RPS (main) | CE | TVD | Spearman | Pearson |\n| --- | --- | --- | --- | --- | --- |')
    Q = r['paired']
    for a, b, nm in (('corr_mixture_pearson', 'ce_mixture', 'mixture ② (Pearson) − mixture ④'), ('corr_mixture_spearman', 'ce_mixture', 'mixture ② (Spearman) − mixture ④'), ('corr_single', 'ce_single', 'best single ② − best single ④')):
        k = lambda met: f'{met}: {a} minus {b}'
        kc = lambda met: f'{met} (test-set correlation, task-attributed): {a} minus {b}'
        o.append(f"| {nm} | {pr(Q,k('rps'))} | {pr(Q,k('ce'),3)} | {pr(Q,k('tvd'))} | {pr(Q,kc('spearman'),3)} | {pr(Q,kc('pearson'),3)} |")
    o.append('')
    o.append('Mean weights (candidate order ' + ', '.join(r['candidate_order']) + '): ② Pearson mixture ' + str([round(x, 3) for x in r['mean_weights']['corr_mixture_pearson']]) + '; ④ mixture ' + str([round(x, 3) for x in r['mean_weights']['ce_mixture']]) + '. Single-judge picks (of 1,000 splits): ② ' + json.dumps(r['single_judge_choice_counts']['corr_single']) + '; ④ ' + json.dumps(r['single_judge_choice_counts']['ce_single']) + '.\n')
o.append('## What the bigger pool changes (all 8 minus old 5, same splits, paired task bootstrap)\n')
o.append('| Method | RPS | CE | TVD |\n| --- | --- | --- | --- |')
E=X['pool_effect_all8_minus_old5']
for m in ('corr_mixture_pearson', 'ce_mixture', 'equal_mixture'):
    o.append(f"| {L[m]} | {pr(E,'rps: '+m)} | {pr(E,'ce: '+m,3)} | {pr(E,'tvd: '+m)} |")
o.append('\nA negative RPS or TVD change is an improvement. Every interval includes zero on RPS: the extra judges do not measurably help either method.\n')
o.append('## Each judge alone against the human mean rating (all 75 artifacts, no fitting)\n')
o.append('| Judge | Pearson | Spearman | mean abs error (0–1 scale) | mean RPS | mean CE |\n| --- | --- | --- | --- | --- | --- |')
for j, v in X['judge_vs_human_all75'].items():
    o.append(f"| {j} | {f(v['pearson'],3)} | {f(v['spearman'],3)} | {f(v['mean_abs_error_0_1'],3)} | {f(v['mean_rps_single'])} | {f(v['mean_ce_single'],2)} |")
o.append('\nThese use all 75 artifacts, including those the split would hold out, and the prompt demos for the cached exp-100 judges came from the original train split (leakage caveat below), so they describe each judge, not generalization.\n')
fs = R['all8']['fixed_split']
o.append('## One fixed split, frontier agent as optimizer\n')
o.append(f"Test tasks: {', '.join(fs['test_tasks'])}. Two gpt-6-astra agents (reasoning effort high, minimal custom tool loop with a python tool; see `agent/`) each got only the 60 train artifacts with all 8 judges' call histograms and the human ratings, and one instruction: ② maximize train Pearson, ④ minimize train cross-entropy over mixtures of the judges (plus the train marginal). They wrote a spec of weights; the scoring script applied it to the 15 test artifacts.\n")
o.append('| Method | RPS (main) | CE | TVD | Spearman | Pearson |\n| --- | --- | --- | --- | --- | --- |')
for nm, key in (('② agent', 'corr'), ('④ agent', 'ce')):
    t = A['agents'][key]['test']; o.append(f"| {nm} | {f(t['rps'])} | {f(t['ce'],3)} | {f(t['tvd'])} | {f(t['spearman'],3)} | {f(t['pearson'],3)} |")
for nm, key in (('② coded optimizer (Pearson mixture)', 'corr_mixture_pearson'), ('④ coded optimizer (CE mixture)', 'ce_mixture')):
    t = fs['test'][key]; o.append(f"| {nm} | {f(t['rps'])} | {f(t['ce'],3)} | {f(t['tvd'])} | {f(t['spearman'],3)} | {f(t['pearson'],3)} |")
FA = X['fixed_split_agents']
o.append(f"\nAgent ② minus agent ④ (task bootstrap over the 5 test tasks): RPS {pr(FA,'rps: agent2 minus agent4')}, CE {pr(FA,'ce: agent2 minus agent4',3)}, TVD {pr(FA,'tvd: agent2 minus agent4')}. Correlations over 15 artifacts are not bootstrapped. Weights: ② agent {json.dumps({k: round(v, 3) for k, v in A['agents']['corr']['weights'].items() if v})}; ④ agent {json.dumps({k: round(v, 3) for k, v in A['agents']['ce']['weights'].items() if v})}.\n")
o.append('## Spend and what was not checked\n')
o.append('- Judge calls: 675 (3 judges × 75 artifacts × 3 calls), all completed; about $10.82 (gpt-6-astra), $1.88 (gpt-6.1-sol), $7.53 (gemini-4-argon) = $20.23. Agents: $0.28. Total about $20.51 against the $300 cap. Computed from token usage times assumed list prices (Astra $10/$50, Sol 6.1 $2/$10, Argon $2/$10 per million tokens), not from provider billing. Earlier failed attempts (key probes, a Codex run that could not start) are not in this number.')
o.append('- No Opus judge was added: no Anthropic API key or Vals route worked. The pool has the 2 cached Opus 5.5 judges only.')
o.append('- Leakage: the cached exp-100 judges (H0/H1/H2) were built with prompts and demos that used the original train split\'s ratings. The three new judges use the same H2 prompt with leave-task-out rated demos, whose human ratings come from other tasks that can be test tasks in a given split, so the same caveat applies.')
o.append('- Only 25 tasks (5 test tasks per split) and one fixed split for the agents; the agent comparison is anecdotal. The harness is a minimal custom loop with the OpenAI Responses API, not Codex.')
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'results.md'), 'w').write('\n'.join(o) + '\n')
print('ok', len('\n'.join(o)))
