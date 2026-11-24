#!/usr/bin/env python3
"""Experiment 25, supplement (dated 11-24-2026): pooled-set-aware checks. CPU only; reads private inputs, writes aggregates only.

Pooling two rating sets that differ in level (new items rate much higher) can make a judge look better than a constant just because the
constant ignores the set. This script gives (1) a set-aware constant baseline (leave-one-task-out inside each set), (2) Spearman/Pearson
computed with ranks taken inside each set, (3) the bootstrap share of draws in which judge A beats judge B on RPS (decision rule c),
(4) mean judge-minus-human bias per set.
Run: python3 setaware.py --old-dataset P --exp21-scores P --sheets DIR --new-judge NAME=FILE ... --pair "Name=old:new" ... --out DIR
"""
import argparse, json, sys
from pathlib import Path
import numpy as np
from scipy import stats
sys.path.insert(0, str(Path(__file__).parent))
from analyze import load_old, load_new, arrays
from evalcore import per_artifact, loto_constant, corr_pair, _pearson


def within_set_corr(jm, hm, setid, idx):
    js, hs = [], []
    for s in (0, 1):
        m = idx[setid[idx] == s]
        if len(m) < 3:
            continue
        js.append(stats.rankdata(jm[m]) / len(m)); hs.append(stats.rankdata(hm[m]) / len(m))
    j = np.concatenate(js); h = np.concatenate(hs)
    return _pearson(j, h)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--old-dataset", required=True); ap.add_argument("--exp21-scores", required=True)
    ap.add_argument("--sheets", required=True); ap.add_argument("--new-judge", action="append", default=[])
    ap.add_argument("--pair", action="append", default=[]); ap.add_argument("--out", required=True)
    ap.add_argument("--draws", type=int, default=10000); ap.add_argument("--min-new-ratings", type=int, default=2)
    a = ap.parse_args()
    old = load_old(a.old_dataset, a.exp21_scores)
    new = load_new(a.sheets, dict(x.split("=", 1) for x in a.new_judge))
    res = {}
    cache = {}
    for pr in a.pair:
        nm, v = pr.split("=", 1); o, n = v.split(":")
        _, Po, Co, Qo, jmo, hmo, to = arrays(old, o, 1)
        _, Pn, Cn, Qn, jmn, hmn, tn = arrays(new, n, a.min_new_ratings)
        cache[nm] = (to, tn, per_artifact(Po, Qo)["RPS"], per_artifact(Pn, Qn)["RPS"])
        Qco, Qcn = loto_constant(Co, to), loto_constant(Cn, tn)
        rc = np.concatenate([per_artifact(Po, Qco)["RPS"], per_artifact(Pn, Qcn)["RPS"]])
        rj = np.concatenate([per_artifact(Po, Qo)["RPS"], per_artifact(Pn, Qn)["RPS"]])
        jm = np.concatenate([jmo, jmn]); hm = np.concatenate([hmo, hmn])
        tasks = np.concatenate([to, tn]); setid = np.concatenate([np.zeros(len(to), int), np.ones(len(tn), int)])
        ut = sorted(set(tasks)); idx_by = {t: np.where(tasks == t)[0] for t in ut}
        rng = np.random.default_rng(20261124)

        def fn(ix):
            return {"RPS_judge": rj[ix].mean(), "RPS_setconst": rc[ix].mean(), "dRPS_vs_setconst": rj[ix].mean() - rc[ix].mean(),
                    "Spearman_withinset_ranks": within_set_corr(jm, hm, setid, ix),
                    "bias_old": (jm[ix][setid[ix] == 0] - hm[ix][setid[ix] == 0]).mean() * 5,
                    "bias_new": (jm[ix][setid[ix] == 1] - hm[ix][setid[ix] == 1]).mean() * 5}
        point = fn(np.arange(len(tasks))); out = {k: [] for k in point}
        for _ in range(a.draws):
            pick = rng.integers(0, len(ut), len(ut)); ix = np.concatenate([idx_by[ut[i]] for i in pick])
            for k, x in fn(ix).items():
                out[k].append(x)
        res[nm] = {k: {"est": float(point[k]), "lo": float(np.nanpercentile(out[k], 2.5)), "hi": float(np.nanpercentile(out[k], 97.5))} for k in point}
        res[nm]["n_old"] = int(len(to)); res[nm]["n_new"] = int(len(tn))
    # decision rule (c): share of task-bootstrap draws where judge A has lower RPS than judge B
    names = list(cache)
    if len(names) == 2:
        A, B = names
        for label, sel in (("old", 2), ("new", 3)):
            ta, tb = cache[A][sel - 2], cache[B][sel - 2]
            ra, rb = cache[A][sel], cache[B][sel]
            assert (ta == tb).all()
            ut = sorted(set(ta)); idx_by = {t: np.where(ta == t)[0] for t in ut}; rng = np.random.default_rng(5)
            w = 0
            for _ in range(a.draws):
                pick = rng.integers(0, len(ut), len(ut)); ix = np.concatenate([idx_by[ut[i]] for i in pick])
                w += rb[ix].mean() < ra[ix].mean()
            res.setdefault("share_B_better_RPS", {})[label] = {"A": A, "B": B, "share_of_draws_B_lower_RPS": w / a.draws,
                                                              "RPS_A": float(ra.mean()), "RPS_B": float(rb.mean())}
    Path(a.out).mkdir(parents=True, exist_ok=True)
    json.dump(res, open(Path(a.out) / "setaware.json", "w"), indent=1)
    print(json.dumps(res, indent=1))


if __name__ == "__main__":
    main()
