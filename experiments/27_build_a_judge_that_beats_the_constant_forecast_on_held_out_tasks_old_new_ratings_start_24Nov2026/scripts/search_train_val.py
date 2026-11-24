"""Experiment 27, step 2: CE-fitted calibration search on TRAIN, selection on pooled VAL. Never loads test rows. Dated 11-24-2026.

Run: python search_train_val.py --data ../data_11-24-2026 --h3 h3_trainval_vals_codex.jsonl --out ../results/search_log_11-24-2026.json
"""
import argparse, itertools, json, sys
import numpy as np
sys.path.insert(0, __import__("os").path.dirname(__file__))
from judgelib import *

ap = argparse.ArgumentParser()
ap.add_argument("--data", required=True); ap.add_argument("--h3", nargs="*", default=[]); ap.add_argument("--out", required=True)
a = ap.parse_args()
D = load(a.data, a.h3, include_test=False)
tr = np.where(D["split"] == "train")[0]; va = np.where(D["split"] == "val")[0]
print("train", len(tr), "val", len(va), "h3 coverage train/val", np.isfinite(D["h3s"][tr]).mean(), np.isfinite(D["h3s"][va]).mean())
Pv = D["P"][va]
log = []


def score(name, model_or_Q, kind):
    Q = model_or_Q
    m = metrics_rows(Pv, Q)
    r = {"name": name, "kind": kind, "val_RPS": float(m["RPS"].mean()), "val_CE": float(m["CE"].mean()), "val_TVD": float(m["TVD"].mean())}
    log.append(r); return r


# baselines on val (constant from train only)
const = marginal(D["C"][tr])
score("BASE_constant_train_pooled", np.tile(const, (len(va), 1)), "baseline")
score("BASE_uniform", np.full((len(va), 6), 1 / 6), "baseline")
score("BASE_H2_raw_astra_opus", D["H2raw"][va], "baseline")
cs = {s: marginal(D["C"][tr][D["set"][tr] == s]) for s in ("old", "new")}
score("BASE_constant_train_per_set", np.array([cs[s] for s in D["set"][va]]), "baseline")

have_h3 = np.isfinite(D["h3s"][tr]).all() and np.isfinite(D["h3s"][va]).all()
for fname, cols in FEATS.items():
    if any(c.startswith("h3") for c in cols) and not have_h3:
        continue
    for alpha, m in itertools.product([0, 0.1, 1, 10], [0, 0.25, 0.5]):
        mod = Ordinal(cols, alpha, m).fit(D, tr)
        r = score(f"{fname}|alpha={alpha}|mix={m}", mod.predict(D, va), "ordinal")
        r.update(feature_set=fname, alpha=alpha, mix=m, set_aware=fname in SET_AWARE, train_CE=mod.train_ce)
if have_h3:
    mod = Direct().fit(D, tr)
    r = score("DIRECT_h3dist", mod.predict(D, va), "direct"); r.update(feature_set="DIRECT", set_aware=False, train_CE=mod.train_ce, beta=float(np.exp(mod.v[0])), gamma=float(np.exp(mod.v[1])))
elig = [r for r in log if r["kind"] in ("ordinal", "direct") and not r.get("set_aware")]
elig.sort(key=lambda r: (round(r["val_RPS"], 6), r["val_CE"]))
sel = elig[0]
for r in sorted(log, key=lambda r: r["val_RPS"])[:25]:
    print(f'{r["name"]:45s} RPS {r["val_RPS"]:.4f} CE {r["val_CE"]:.4f} TVD {r["val_TVD"]:.4f}' + ("  [set-aware]" if r.get("set_aware") else ""))
print("SELECTED", sel["name"])
json.dump({"date": "11-24-2026", "selected": sel, "n_candidates": len(log), "log": log}, open(a.out, "w"), indent=1)
