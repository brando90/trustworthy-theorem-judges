"""Read results/raw.jsonl + population.json; write results.md, results/summary.json, figures."""
import os, json, sys
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np
from scipy.optimize import least_squares
from scipy.special import softmax
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
import toy

H = os.path.join(os.path.dirname(__file__), '..'); R = f'{H}/results'
rows = [json.loads(l) for l in open(f'{R}/raw.jsonl')]
pop = json.load(open(f'{R}/population.json'))
FITS = toy.FITS; NAMES = {'ce': 'CE fit (④)', 'rps': 'RPS fit', 'pearson': 'Pearson fit (②, raw)', 'pearson_head': 'Pearson fit + calibrated head'}
COL = {'ce': '#1b6ca8', 'rps': '#6a9f3a', 'pearson': '#d9534f', 'pearson_head': '#e08a1e'}
NS = sorted({r['n'] for r in rows}); MET = ['rps_excess', 'ce_excess', 'tvd', 'spearman', 'pearson', 'rps', 'ce']
rng = np.random.default_rng(0)

def arr(sc, fit, met, n):
    return np.array([r[fit][met] for r in rows if r['scenario'] == sc and r['n'] == n], float)
def mean_ci(v, B=2000):
    v = v[~np.isnan(v)]; m = v.mean(); bs = rng.choice(v, (B, len(v))).mean(1)
    return m, *np.percentile(bs, [2.5, 97.5])
def pl(n, E, A, a): return E + A * n ** (-a)
def fit_pl(n, y):
    best = None
    for a0 in (0.3, 1.0, 2.0):
        r = least_squares(lambda p: np.log(pl(n, *p) + 1e-12) - np.log(y), [y[-1] * .5, y[0] * n[0] ** a0, a0],
                          bounds=([0, 0, 0], [10, 1e6, 4]))
        if best is None or r.cost < best.cost: best = r
    return best.x
def need(E, A, a, d):
    return (A / (d - E)) ** (1 / a) if d > E and a > 0 else np.inf

out = {}; md = []
NFIT = [n for n in NS if n >= 16]; TARGET = {'rps_excess': [0.01, 0.003], 'ce_excess': [0.05]}
for sc in 'AB':
    for fit in FITS:
        for met in ['rps_excess', 'ce_excess']:
            curve = np.array([arr(sc, fit, met, n).mean() for n in NFIT])
            E, A, a = fit_pl(np.array(NFIT, float), curve)
            pers = {n: arr(sc, fit, met, n) for n in NFIT}; bsp = []
            for _ in range(300):
                c = np.array([rng.choice(pers[n], len(pers[n])).mean() for n in NFIT]); bsp.append(fit_pl(np.array(NFIT, float), c))
            bsp = np.array(bsp)
            d = dict(E=E, A=A, alpha=a, E_ci=np.percentile(bsp[:, 0], [2.5, 97.5]).tolist(), alpha_ci=np.percentile(bsp[:, 2], [2.5, 97.5]).tolist())
            for t in TARGET[met]:
                nn = need(E, A, a, t); bn = np.array([need(*b, t) for b in bsp[:, [0, 1, 2]]])
                d[f'n_for_{t}'] = nn; d[f'n_for_{t}_ci'] = [float(np.percentile(bn, 2.5)), float(np.percentile(bn, 97.5))]
                d[f'frac_unreachable_{t}'] = float(np.mean(~np.isfinite(bn)))
            out[f'{sc}/{fit}/{met}'] = d

def fmt_n(v): return 'not reached (floor above target)' if not np.isfinite(v) else f'{v:,.0f}'
def fmt_ci(ci): return f'[{ci[0]:,.0f}, {"inf" if not np.isfinite(ci[1]) else format(ci[1], ",.0f")}]'

md.append('# Results, experiment 13: toy, Pearson fit vs cross-entropy fit on nonlinear synthetic ratings\n')
md.append('**TOY, works by construction. An illustration of the argument, not evidence about the real ratings.** CPU only, $0, numpy/scipy (Claude Code worker, Sonnet 5.5, 11-10-2026). No LLM judge is involved: the "judge" is a fitted function of one feature.\n')
md.append('## Setup (details in README.md)\n')
md.append('- Each task has a feature x in [-1, 1]. Human ratings 0 to 5 follow a beta-binomial whose spread depends nonlinearly on x: kappa(x) = exp(1.5 + 2.2 cos(1.5 pi x)), from U-shaped (disagreement) to tight.')
md.append('- **Scenario A, same mean:** human mean 2.1 to 2.9 on a small linear drift in x, so the mean says almost nothing while the spread changes a lot.')
md.append('- **Scenario B, monotone nonlinear mean:** human mean = 5(0.1 + 0.8((x+1)/2)^2), plus the same spread pattern. Spearman and Pearson are both high for any judge that gets the mean right.')
md.append('- Every judge: softmax of a linear map of 13 cosine/sine features (same class). Fits differ only in the objective on the n training tasks (k = 3 raters each, empirical histogram): **CE** (④), **RPS** (second proper score), **Pearson** of the judge\'s mean vs the human mean (②), and **Pearson + head** (Pearson-fit score, then an ordinal head fitted by CE on that one scalar, the "score, then calibrate" practice). Same ridge c/n for all.')
md.append(f'- Test: 500 fresh tasks per seed, scored against the TRUE distribution. Excess = loss minus the loss of the true distribution (excess RPS = mean over the 5 thresholds of (Qc-Pc)^2; excess CE = KL). 100 seeds per n; intervals are 95% bootstrap over seeds (train and test tasks are redrawn each seed, so this plays the role of the task bootstrap). n from {", ".join(map(str, NS))}.\n')

for sc, title in [('A', 'Scenario A (same mean, spread varies)'), ('B', 'Scenario B (monotone nonlinear mean, spread varies)')]:
    md.append(f'## {title}: held-out metrics by number of training tasks\n')
    for n in [20, 64, 256, 2048]:
        md.append(f'**n = {n} training tasks** (mean over 100 seeds [95% CI]); RPS excess first (lower better)\n')
        md.append('| fit | RPS excess | CE excess | TVD | Spearman | Pearson |'); md.append('|---|---|---|---|---|---|')
        for fit in FITS:
            c = []
            for met in ['rps_excess', 'ce_excess', 'tvd', 'spearman', 'pearson']:
                m, lo, hi = mean_ci(arr(sc, fit, met, n)); c.append(f'{m:.4f} [{lo:.4f}, {hi:.4f}]' if met in ('rps_excess', 'ce_excess', 'tvd') else f'{m:.3f} [{lo:.3f}, {hi:.3f}]')
            md.append(f'| {NAMES[fit]} | ' + ' | '.join(c) + ' |')
        md.append('')
    md.append('**n to infinity** (fit on a dense grid of tasks with the true distributions, no sampling noise, ridge to 0):\n')
    md.append('| fit | RPS excess | CE excess | TVD | Spearman | Pearson |'); md.append('|---|---|---|---|---|---|')
    for fit in FITS:
        p = pop[sc][fit]; md.append(f'| {NAMES[fit]} | ' + ' | '.join('nan' if np.isnan(p[m]) else f'{p[m]:.4f}' for m in ['rps_excess', 'ce_excess', 'tvd', 'spearman', 'pearson']) + ' |')
    md.append('')

md.append('## Power-law fit and the number of training tasks needed\n')
md.append('Form fitted, per scenario and fit: **excess(n) = E + A n^(-alpha)**, nonlinear least squares in log space on the seed-mean curve over n >= 16, E >= 0 (a floor), alpha in [0, 4]. Intervals: 300 bootstrap resamples of the seeds. n needed = (A / (target - E))^(1/alpha), "not reached" when the fitted floor E is at or above the target. This is an empirical curve fit to simulated data, **not a proven bound**; it holds only for this toy, this function class and k = 3 raters per task; it says nothing about misspecified classes, other noise, or the real ratings. Targets: 0.01 RPS and 0.05 CE above the true distribution; a stricter 0.003 RPS target is added because the 0.01 target turns out not to separate the fits.\n')
for sc in 'AB':
    md.append(f'**Scenario {sc}**\n')
    md.append('| fit | metric | alpha [95% CI] | floor E [95% CI] | n for target | 95% CI of n |'); md.append('|---|---|---|---|---|---|')
    for fit in FITS:
        for met in ['rps_excess', 'ce_excess']:
            d = out[f'{sc}/{fit}/{met}']
            if d['alpha'] >= 3.99:     # fit ran into its bound: the curve does not decay (it rises as the ridge weakens)
                md.append(f"| {NAMES[fit]} | {met} | n/a: curve does not decay with n (rises as the ridge c/n weakens), power law not applicable | | not reached | |"); continue
            for t in TARGET[met]:
                md.append(f"| {NAMES[fit]} | {met} <= {t} | {d['alpha']:.2f} [{d['alpha_ci'][0]:.2f}, {d['alpha_ci'][1]:.2f}] | {d['E']:.4f} [{d['E_ci'][0]:.4f}, {d['E_ci'][1]:.4f}] | {fmt_n(d[f'n_for_{t}'])} | {fmt_ci(d[f'n_for_{t}_ci'])} (unreachable in {d[f'frac_unreachable_{t}']:.0%} of resamples) |")
    md.append('')
md.append('Sanity reference, not fitted: for a well-specified parametric model the excess CE is about (free parameters)/(2 x number of ratings) = 65/(2 x 3n), about 11/n, which would mean alpha = 1. It matches the CE fit in size (scenario A at n = 256: about 0.043 predicted, 0.039 measured; at n = 2048: 0.0053 predicted, 0.0065 measured), but the fitted exponents over n = 16 to 2048 are lower (0.6 to 0.9). Over this range the curve is probably not yet in its asymptotic regime (a guess, not tested), so extrapolating far beyond n = 2048 or below n = 16 would be unsafe. Intervals here cover seed noise only, not the choice of functional form or of the fitting range.\n')

# figure 1
fig, axs = plt.subplots(2, 2, figsize=(11, 8), sharex=True)
for i, sc in enumerate('AB'):
    for j, met in enumerate(['rps_excess', 'ce_excess']):
        ax = axs[i, j]
        for fit in FITS:
            ms = np.array([mean_ci(arr(sc, fit, met, n)) for n in NS])
            ax.plot(NS, ms[:, 0], 'o-', color=COL[fit], label=NAMES[fit], ms=3); ax.fill_between(NS, ms[:, 1], ms[:, 2], color=COL[fit], alpha=.15)
            ax.axhline(pop[sc][fit][met], color=COL[fit], ls=':', lw=1)
            if fit == 'ce':
                d = out[f'{sc}/{fit}/{met}']; xs = np.logspace(np.log10(16), np.log10(2048), 50); ax.plot(xs, pl(xs, d['E'], d['A'], d['alpha']), 'k--', lw=1, label='power law fit (CE fit)')
        for t in TARGET[met][:1]: ax.axhline(t, color='gray', lw=1); ax.text(NS[0], t * 1.08, f'target {t}', color='gray', fontsize=8)
        ax.set_xscale('log'); ax.set_yscale('log'); ax.set_title(f"{'A: same mean' if sc == 'A' else 'B: monotone nonlinear mean'}: held-out {met.replace('_', ' ')}"); ax.set_xlabel('training tasks n'); ax.set_ylabel('excess over true distribution (lower better)')
axs[0, 0].legend(fontsize=7); fig.suptitle('Toy (works by construction): dotted = n to infinity limit of each fit', fontsize=10); fig.tight_layout(); fig.savefig(f'{H}/fig_excess_vs_n.png', dpi=130)

# figure 2: fitted vs true distributions at 3 values of x (n = 1024, seed 0, scenario A)
n = 1024; r0 = np.random.default_rng(5); x = r0.uniform(-1, 1, n); Pt = toy.truth(x, 'A'); P = np.array([r0.multinomial(3, p) for p in Pt]) / 3
Phi = toy.phi(x); W0 = toy.marginal_W0(Phi, P, 0); Wc = toy.fit(Phi, P, 'ce', n, W0); Wp = toy.fit(Phi, P, 'pearson', n, W0)
s = softmax(Phi @ Wp, 1) @ toy.GRID; m, sd = s.mean(), s.std(); Hh = np.stack([np.ones(n), (s - m) / sd], 1); Wh = toy.fit(Hh, P, 'ce', n, toy.marginal_W0(Hh, P, 0))
xs = np.array([-0.7, 0.0, 0.5]); fig, axs = plt.subplots(1, 3, figsize=(12, 3.4), sharey=True)
st = softmax(toy.phi(xs) @ Wp, 1) @ toy.GRID; Qh = softmax(np.stack([np.ones(3), (st - m) / sd], 1) @ Wh, 1)
for a, xv, tp, qc, qh in zip(axs, xs, toy.truth(xs, 'A'), softmax(toy.phi(xs) @ Wc, 1), Qh):
    w = .27; a.bar(toy.GRID - w, tp, w, color='k', label='human (true)'); a.bar(toy.GRID, qc, w, color=COL['ce'], label='CE fit'); a.bar(toy.GRID + w, qh, w, color=COL['pearson_head'], label='Pearson + head')
    a.set_title(f'x = {xv}: human mean {tp @ toy.GRID:.2f}'); a.set_xlabel('rating')
axs[0].legend(fontsize=8); axs[0].set_ylabel('probability'); fig.suptitle('Scenario A, n = 1024 training tasks: similar means, different spread (one seed)', fontsize=10); fig.tight_layout(); fig.savefig(f'{H}/fig_distributions.png', dpi=130)

open(f'{H}/results.md', 'w').write('\n'.join(md))
json.dump({k: {a: (b if not isinstance(b, float) or np.isfinite(b) else None) for a, b in v.items()} for k, v in out.items()}, open(f'{R}/summary.json', 'w'), indent=1)
print('ok')
