#!/usr/bin/env python3
"""TLDR: Render results.md (aggregate tables only) from results/metrics.json and results/scaling.json."""
import argparse, json

LABEL = {'H0_sol': 'H0 Sol', 'H0_opus': 'H0 Opus', 'H1_sol': 'H1 Sol', 'H2_sol': 'H2 Sol', 'H2_opus': 'H2 Opus'}
FAM = ['nrmse', 'sqrt_rps', 'kl', 'pearson', 'spearman', 'kendall']
HEAD = {'nrmse': 'nRMSE', 'sqrt_rps': 'sqrt RPS', 'kl': 'KL', 'const_nrmse': 'constant nRMSE', 'pearson': 'Pearson', 'spearman': 'Spearman', 'kendall': 'Kendall'}


def f(x, d=3):
    return f'{x:.{d}f}'


def cell(m, d=3):
    return f"{f(m['point'], d)} [{f(m['lo'], d)}, {f(m['hi'], d)}]"


def table(v):
    cols = ['nrmse', 'const_nrmse', 'sqrt_rps', 'kl', 'pearson', 'spearman', 'kendall']
    out = ['| Judge | ' + ' | '.join(HEAD[c] for c in cols) + ' |', '|---|' + '---:|' * len(cols)]
    for j, m in v['metrics'].items():
        out.append(f'| {LABEL[j]} | ' + ' | '.join(cell(m[c], 3 if c != 'kl' else 2) for c in cols) + ' |')
    return '\n'.join(out)


def sci(x):
    return f'{x:.3g}'


def main():
    ap = argparse.ArgumentParser(); ap.add_argument('--metrics', required=True); ap.add_argument('--scaling', required=True); ap.add_argument('--out', required=True)
    a = ap.parse_args()
    M = json.load(open(a.metrics)); S = json.load(open(a.scaling))
    P = M['variants']['expert_all75']
    L = []
    w = L.append
    w('# Experiment 07: Experiment 1 metric table and scaling fit on cached judge scores\n')
    w('**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/07_compare_5_judges_on_75_outputs_and_estimate_rating_needs/results.md>\n')
    w('**TLDR:** Five cached scalar judges, 75 artifacts, 25 tasks, 195 expert ratings, zero new model calls, no paid API. All numbers below were computed by CPU scripts in this folder (Python 3, numpy, scipy), not by a model; the cached judge scores themselves come from the historical runs named in the table below.\n')
    w('## 1. Which count is right: 343 or 195?\n')
    w('Both describe the same 75 artifacts (25 tasks x 3 agent samples each), different rater panels. Counted from `inputs/items.jsonl` at veribench commit `be287d9`: **195** ratings come from the three expert columns (p1 75, p2 75, p3 45); the two other columns add p4 75 and p5 75, so **345** ratings over five raters (45 artifacts have 5 ratings, 30 have 4). I did not find 343 in the files I searched (`items.jsonl`, the experiment README and PROTOCOL.md, the phase-0 audit, `results/VERIFICATION.json`); the 345 here and the 44/75 versus 45/75 for the third rater differ from the notes in the prompt text by 2 and 1. The primary target is the expert panel (195), as PROTOCOL.md of experiment 100 specifies ("mean of available ratings from participants 1-3"); the five-rater panel (345) is secondary. The "25x3x5" tensor shape is tasks x agent samples x raters.\n')
    w('## 2. Method\n')
    w(f"- **Judges (cached, no new calls):** per artifact 3 sampled scalar repeats (integer 0-5), 1,125 historical calls in total. Probabilities come from **sampled repeats**, not digit logprobs: the receipts hold no token probabilities. Judge pmf = histogram of the 3 repeats over ratings 0-5, floored at one eps = **{M['eps']}** and renormalised (the same floor for every metric that uses a pmf).")
    w('- **Judge names (from the run configs):** H0 Sol, H1 Sol, H2 Sol = `openai/gpt-6-sol-high` (reasoning effort high, Vals gateway); H0 Opus, H2 Opus = `anthropic/claude-opus-5-5-no-fallback` at compute_effort=max with adaptive thinking. H0 is the raters\' instructions, H1 adds rater-convention notes, H2 adds expert-rated demonstration examples; prompts were developed on the training split of this same 75-artifact set. Gemini is not a judge in any row. Harness: the veribench experiment-100 judge runner; the numbers here come from this folder\'s Python scripts.')
    w('- **Human target:** expert panel, mean rating / 5 for nRMSE and correlations; empirical pmf of the 2-3 expert ratings per artifact for sqrt RPS and KL.')
    w('- **Metrics:** nRMSE = sqrt(mean over artifacts of (judge mean/5 - human mean/5)^2). sqrt RPS = sqrt(mean over artifacts of (1/5) sum over 5 thresholds of (F_judge - F_human)^2). **KL** = forward KL(q || p) with q the human empirical pmf (more than one rating per artifact, so KL rather than cross-entropy; CE = KL + H(q) is in `results/metrics.json`). Constant nRMSE = nRMSE of predicting the mean human score for every artifact (in-sample best constant, so it is the hardest constant to beat). Pearson, Spearman (average ranks) and Kendall (tau-b) compare the judge mean and the human mean across artifacts. **No R^2.** Artifacts are weighted equally.')
    w(f"- **Uncertainty:** 95% percentile intervals from **{M['bootstrap']:,} task-level bootstrap resamples** (25 tasks drawn with replacement, all of a drawn task's artifacts kept, seed {M['seed']}). Intervals cover task sampling only, not rater or judge-sampling variation, and not the prompt-development exposure.")
    w('- **Tag: no DT.** These cached judges score formal-specification coverage on the original candidate Lean files; no DT variant of the gold or candidates is involved.\n')
    w(f"## 3. Experiment 1 table (expert panel, {P['n_items']} artifacts, {P['n_tasks']} tasks, {P['n_ratings']} ratings; no DT)\n")
    w('nRMSE, constant nRMSE, sqrt RPS and KL: lower is better. Correlations: higher is better. Values: point [95% CI].\n')
    w(table(P)); w('')
    ce = P['ce_point']
    w('Cross-entropy (point, nats, equals KL plus the human entropy): ' + ', '.join(f'{LABEL[j]} {ce[j]:.2f}' for j in ce) + '. KL and CE are large because three sampled repeats put zero mass on most ratings and the eps floor of 1e-3 costs about 6.9 nats per unsupported rating; they move with eps and must not be compared across eps values.\n')
    worse = [LABEL[j] for j, m in P['metrics'].items() if m['nrmse']['point'] >= m['const_nrmse']['point'] - 0.01]
    w('Against the constant guess: ' + ', '.join(f"{LABEL[j]} {m['nrmse']['point']:.3f} vs {m['const_nrmse']['point']:.3f}" for j, m in P['metrics'].items()) + '. Judges within 0.01 of the constant (or worse): ' + (', '.join(worse) if worse else 'none') + '. The intervals of judge and constant overlap for every judge; no paired judge-minus-constant interval was computed.\n')
    R = P['ranking']
    w('### Does the judge ranking change between metric families?\n')
    w('Best to worst by point estimate:\n')
    w('| Metric | Order | P(best) in bootstrap |'); w('|---|---|---|')
    for m in FAM:
        w(f"| {HEAD[m]} | {' > '.join(LABEL[j] for j in R['order_best_to_worst'][m])} | " + ', '.join(f"{LABEL[j]} {p:.2f}" for j, p in R['p_rank1'][m].items() if p > 0) + ' |')
    w('')
    nz = {m: [k for k, v in R['paired'][m].items() if v['excludes_zero']] for m in FAM}
    w('Paired bootstrap differences between judges (10 pairs per metric) whose 95% interval excludes zero: ' + '; '.join(f"{HEAD[m]}: {len(nz[m])}" + (' (' + ', '.join(nz[m]) + ')' if nz[m] else '') for m in FAM) + '.\n')
    w('Kendall tau between the point-estimate rankings of two metrics: ' + ', '.join(f'{k} {v:.2f}' for k, v in R['tau_between_metric_rankings'].items()) + '.\n')
    w('Reading: see the order table. Where the order differs between families, the intervals decide whether the difference is resolved; with 25 tasks and 5 judges most pairwise differences are not resolved, so no claim is made that the probability-based metrics (sqrt RPS, KL) rank judges better than the correlations or nRMSE.\n')
    for vn, title in (('expert_valtest', 'Secondary A: expert panel, validation + test artifacts only (judge prompts were developed on the training split)'), ('all5_all75', 'Secondary B: all five raters (345 ratings)')):
        v = M['variants'][vn]
        w(f"## {title}\n"); w(f"{v['n_items']} artifacts, {v['n_tasks']} tasks, {v['n_ratings']} ratings; same method and {M['bootstrap']:,} resamples.\n")
        w(table(v)); w('')
        w('Order by nRMSE: ' + ' > '.join(LABEL[j] for j in v['ranking']['order_best_to_worst']['nrmse']) + '; by sqrt RPS: ' + ' > '.join(LABEL[j] for j in v['ranking']['order_best_to_worst']['sqrt_rps']) + '; by KL: ' + ' > '.join(LABEL[j] for j in v['ranking']['order_best_to_worst']['kl']) + '.\n')
    # scaling
    fp = S['fit_pooled']
    w('## 4. Scaling fit by subsampling the same ratings\n')
    w('**Reading used (open with Brando: N and D were not defined on the whiteboard).** The cached judges are not trained on tasks or ratings, so l is the squared **estimation error of a judge\'s nRMSE** (scores/5): evaluate on n tasks with k human ratings per artifact and m judge repeats, and compare with the value on the 13 disjoint held-out tasks using all ratings and m=3. N = n tasks, D = k human ratings per artifact (3 n k ratings in total per evaluation). The five-rater panel is used so that k = 1..4 exists for every artifact. l is averaged over the five judges; per-judge fits are in `results/scaling.json`. Grid: n in {2,3,4,6,8,10,12}, k in {1,2,3,4}, m in {1,2,3}; ' + f"{S['draws']:,} random task/rater/repeat draws (seed {S['seed']}), zero model calls. This measures how fast the measurement error of the metric falls with more tasks and ratings; it does not show how a trained judge improves.\n")
    p = fp['F1']['params']; c = S['ci_mc_F1']
    w('### Fit 1: l = E + A n^-alpha + B k^-beta (m = 3)\n')
    w('| Coefficient | Estimate | 95% CI (Monte-Carlo, see below) |'); w('|---|---:|---|')
    for k in ['E', 'A', 'alpha', 'B', 'beta']:
        w(f'| {k} | {sci(p[k])} | [{sci(c[k][0])}, {sci(c[k][1])}] |')
    w(f"\nFit quality: RMS error of log l over the 28 grid cells = {fp['F1']['fit_rmse_log']:.3f} (a factor of about {2.718281828**fp['F1']['fit_rmse_log']:.2f}); no R^2.\n")
    pred = lambda n, k: (p['E'] + p['A'] * n ** -p['alpha'] + p['B'] * k ** -p['beta']) ** 0.5
    w(f"Predicted sqrt l (RMS error of the estimated nRMSE): observed grid corner n=12, k=4: {pred(12, 4):.3f}; n=2, k=1: {pred(2, 1):.3f}; EXTRAPOLATION n=25, k=5: {pred(25, 5):.3f}.\n")
    p2 = fp['F2']['params']; c2 = S['ci_mc_F2']
    w('### Fit 2: MSE(n,k,m) = E0 + A/n^a + B/k + C/m^b (tasks, raters, judge repeats)\n')
    w('| Coefficient | Estimate | 95% CI (Monte-Carlo) |'); w('|---|---:|---|')
    for k in ['E0', 'A', 'a', 'B', 'C', 'b']:
        w(f'| {k} | {sci(p2[k])} | [{sci(c2[k][0])}, {sci(c2[k][1])}] |')
    w(f"\nFit quality: RMS error of log l over the 84 grid cells = {fp['F2']['fit_rmse_log']:.3f}. Variant with a free k exponent (B/k^beta_k): beta_k = {fp['F2_free_k']['params']['beta_k']:.2f}, RMS log error {fp['F2_free_k']['fit_rmse_log']:.3f}. Parameters at a bound (b = 4, E0 = 0) are not identified. The loss is a squared error, so a 1/k bias term enters squared; the fixed-1/k form is the one requested and is reported as such. Agent count (3 samples per task) is too small for a curve and is not varied.\n")
    w('The Monte-Carlo CI refits the curve on 500 resamples of 40 independent simulation batches; it captures simulation noise only. Task-set sensitivity: leave-5-tasks-out refits of Fit 1 (5 refits) give alpha in ' + f"[{min(x['alpha'] for x in S['task_sensitivity_F1_leave5tasks_out']):.2f}, {max(x['alpha'] for x in S['task_sensitivity_F1_leave5tasks_out']):.2f}] and beta in [{min(x['beta'] for x in S['task_sensitivity_F1_leave5tasks_out']):.2f}, {max(x['beta'] for x in S['task_sensitivity_F1_leave5tasks_out']):.2f}]; with only 25 tasks the exponents are loosely determined.\n")
    w('### n and k needed for a target precision (EXTRAPOLATION beyond n = 12, k = 4)\n')
    w('Target = predicted RMS error of the estimated nRMSE (sqrt l). "Reducible only" removes the floor E (which here is partly the noise of the 13-task reference); "including floor" keeps it. Smallest total ratings 3nk on the fitted curve; all values beyond the observed grid are extrapolation.\n')
    w('| Target sqrt l | Reducible only (n, k, total ratings) | Including floor E |'); w('|---|---|---|')
    for t, r in S['requirement_F1'].items():
        fmt = lambda x: 'not reached for n<=200, k<=40' if x is None else f"n={x['n']}, k={x['k']}, {x['total_ratings']} ratings"
        w(f"| {t} | {fmt(r['reducible_only'])} | {fmt(r['including_floor_E'])} |")
    w('\n## 5. What this does not show\n')
    w('- Judge prompts H0-H2 were developed on the training split of these same artifacts, and the raters and artifacts have prior exposure; the table is retrospective, not a fresh validation.')
    w('- 25 tasks, one solver population, one rater pool; intervals cover task sampling only.')
    w('- Sampled-repeat histograms from 3 calls are a weak probability estimator; KL and sqrt RPS depend on it and on eps.')
    w('- The scaling fit measures metric-estimation precision under one reading of N and D; extrapolations are model-based.')
    open(a.out, 'w').write('\n'.join(L) + '\n')


if __name__ == '__main__':
    main()
