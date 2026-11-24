"""Analysis of experiment 24 exactly as pre-registered (PREREG.md section 5): AG_B, AG_A, boost/penalty, own-family contrast, arm C gap, manipulation checks, ceiling.

Use: python3 scripts/analyze.py after run_judges.py for both judges. Needs python3 only (no numpy). Reads results/<judge>/cells.csv, materials/, writes results/summary.json and results/summary.md.
Scores 0-5; unit = task; paired; 95% percentile bootstrap over tasks, 10,000 resamples, seed 0.
Example: python3 scripts/analyze.py
"""
import csv, json, os, random, sys, pathlib
sys.path.insert(0, os.path.dirname(__file__))
from lean_utils import similarity
HERE = pathlib.Path(__file__).resolve().parents[1]
JUDGES = {'claude': ('claude-opus-5-5', 'Claude Code CLI'), 'codex': ('gpt-6-astra', 'Codex CLI')}


def boot(xs, n=10000, seed=0):
    xs = list(xs)
    if not xs: return None
    rng = random.Random(seed); k = len(xs); m = []
    for _ in range(n): m.append(sum(xs[rng.randrange(k)] for _ in range(k)) / k)
    m.sort(); return dict(n=k, mean=sum(xs) / k, lo=m[int(0.025 * n)], hi=m[int(0.975 * n) - 1])


def verdict(b):
    if b is None: return 'NO DATA'
    if b['lo'] > 0 and b['mean'] >= 0.20: return 'HOLDS'
    if b['lo'] > -0.15 and b['hi'] < 0.15: return 'DOES NOT HOLD'
    return 'INCONCLUSIVE'


def load(judge):
    p = HERE / 'results' / judge / 'cells.csv'
    if not p.exists(): return {}
    s = {}
    for r in csv.DictReader(open(p)):
        if r['score'] != '': s[(r['task'], r['cand'], r['ref'])] = float(r['score'])
    return s


def per_task(s, f):
    out = {}
    for t in {k[0] for k in s}:
        v = f(lambda c, r: s.get((t, c, r)))
        if v is not None: out[t] = v
    return out


def main():
    res, md = {}, []
    for j, (model, harness) in JUDGES.items():
        s = load(j)
        if not s: continue
        other = 'codex' if j == 'claude' else 'claude'
        def ab(g):
            v = [g('G', 'G'), g('Gx', 'Gx'), g('G', 'Gx'), g('Gx', 'G')]
            return None if None in v else (v[0] + v[1] - v[2] - v[3]) / 2
        # arm A needs similarity: computed per task from the files
        def arm_a():
            out = {}
            for t in {k[0] for k in s}:
                gp = HERE / 'materials' / t / f'Gprime_{other}.lean'
                if not gp.exists(): continue
                n = (HERE / 'materials' / t / 'N.lean').read_text()
                sg, sx = similarity(n, (HERE / 'materials' / t / 'G.lean').read_text()), similarity(n, gp.read_text())
                if sg == sx: continue
                a, b = s.get((t, 'N', 'G')), s.get((t, 'N', 'Gx'))
                if a is None or b is None: continue
                out[t] = (a - b) if sg > sx else (b - a)
            return out
        R = {}
        R['AG_B'] = boot(per_task(s, ab).values()); R['AG_A'] = boot(arm_a().values())
        R['verdict_B'], R['verdict_A'] = verdict(R['AG_B']), verdict(R['AG_A'])
        def mean_cell(c, r):
            v = [s[(t, c, r)] for t in {k[0] for k in s} if (t, c, r) in s]; return dict(n=len(v), mean=sum(v) / len(v)) if v else None
        R['cell_means'] = {f'{c}|{r}': mean_cell(c, r) for c, r in sorted({(k[1], k[2]) for k in s})}
        def pair(c, r1, r2):
            return boot([s[(t, c, r1)] - s[(t, c, r2)] for t in {k[0] for k in s} if (t, c, r1) in s and (t, c, r2) in s])
        R['boost_vs_none'] = {f'{c}|{r}-none': pair(c, r, 'none') for c in ('G', 'Gx', 'N', 'H') for r in ('G', 'Gx') if mean_cell(c, 'none')}
        R['own_family_contrast_A'] = pair('N', 'Gown', 'Gx')
        R['armC_gap'] = {r: boot([s[(t, 'N', r)] - s[(t, 'H', r)] for t in {k[0] for k in s} if (t, 'N', r) in s and (t, 'H', r) in s]) for r in ('G', 'Gx', 'none')}
        R['manip_D'] = {'N|G - N|H': boot([s[(t, 'N', 'G')] - s[(t, 'N', 'H')] for t in {k[0] for k in s} if (t, 'N', 'G') in s and (t, 'N', 'H') in s]),
                        'N|G - N|Gother': boot([s[(t, 'N', 'G')] - s[(t, 'N', 'Gother')] for t in {k[0] for k in s} if (t, 'N', 'G') in s and (t, 'N', 'Gother') in s])}
        lit = [s[(t, 'G', 'G')] for t in {k[0] for k in s} if (t, 'G', 'G') in s] + [s[(t, 'Gx', 'Gx')] for t in {k[0] for k in s} if (t, 'Gx', 'Gx') in s]
        R['literal_copy_mean'] = sum(lit) / len(lit) if lit else None
        match = [v for (t, c, r), v in s.items() if (c, r) in (('G', 'G'), ('Gx', 'Gx'), ('G', 'Gx'), ('Gx', 'G'), ('N', 'G'), ('N', 'Gx'))]
        R['share_exact_5_matching_cells'] = sum(1 for v in match if v == 5) / len(match) if match else None
        R['share_ge_4_9'] = sum(1 for v in match if v >= 4.9) / len(match) if match else None
        R['n_cells'] = len(s); R['n_tasks'] = len({k[0] for k in s})
        R['model'], R['harness'] = model, harness
        res[j] = R
    ys = [res[j]['verdict_B'] for j in res]
    overall = 'yes (HOLDS on AG_B for both judges)' if len(ys) == 2 and all(y == 'HOLDS' for y in ys) else 'no (DOES NOT HOLD on AG_B for both judges)' if len(ys) == 2 and all(y == 'DOES NOT HOLD' for y in ys) else 'inconclusive'
    res['overall_FSC'] = overall
    json.dump(res, open(HERE / 'results/summary.json', 'w'), indent=1)
    f = lambda b: 'n/a' if b is None else f"{b['mean']:+.3f} [{b['lo']:+.3f}, {b['hi']:+.3f}] (n={b['n']})"
    md.append(f'Overall verdict on FSC (no DT; AG_B both judges): **{overall}**\n')
    md.append('| Judge (harness, model) | AG_B twins, exact match | verdict | AG_A natural, similarity | verdict |\n|---|---|---|---|---|')
    for j in JUDGES:
        if j in res: R = res[j]; md.append(f"| {R['harness']}, {R['model']} | {f(R['AG_B'])} | {R['verdict_B']} | {f(R['AG_A'])} | {R['verdict_A']} |")
    for j in JUDGES:
        if j not in res: continue
        R = res[j]; md.append(f"\n**{R['harness']}, {R['model']}**: {R['n_tasks']} tasks, {R['n_cells']} scored cells; literal-copy mean {R['literal_copy_mean']}; share of exact 5 in matching cells {R['share_exact_5_matching_cells']}")
        md.append('| cell (candidate|reference) | n | mean |\n|---|---|---|')
        for k, v in R['cell_means'].items(): md.append(f"| {k} | {v['n']} | {v['mean']:.3f} |")
        md.append('| contrast | mean [95% CI] |\n|---|---|')
        for k, v in R['boost_vs_none'].items(): md.append(f'| {k} | {f(v)} |')
        md.append(f"| own-family G'own - G'x (arm A) | {f(R['own_family_contrast_A'])} |")
        for k, v in R['armC_gap'].items(): md.append(f'| arm C gap N-H under ref {k} | {f(v)} |')
        for k, v in R['manip_D'].items(): md.append(f'| manipulation {k} | {f(v)} |')
    open(HERE / 'results/summary.md', 'w').write('\n'.join(md) + '\n')
    print('\n'.join(md))


if __name__ == '__main__':
    main()
