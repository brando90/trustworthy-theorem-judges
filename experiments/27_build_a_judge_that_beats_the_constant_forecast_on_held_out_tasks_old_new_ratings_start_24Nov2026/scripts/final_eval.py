"""Experiment 27, step 3: single held-out TEST evaluation of the frozen config. Dated 11-24-2026.

Reads the frozen selection from the search log, refits on train+val, scores test once, task bootstrap (10,000 draws, seed 20261124).
Run only after the freeze commit. python final_eval.py --data ../data_11-24-2026 --h3 h3_trainval_vals_codex.jsonl h3_test_vals_codex.jsonl --search ../results/search_log_11-24-2026.json --out ../results/test_results_11-24-2026.json
"""
import argparse, json, sys, os
import numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from judgelib import *

ap = argparse.ArgumentParser()
ap.add_argument("--data", required=True); ap.add_argument("--h3", nargs="*", default=[]); ap.add_argument("--search", required=True); ap.add_argument("--out", required=True)
ap.add_argument("--draws", type=int, default=10000)
a = ap.parse_args()
sel = json.load(open(a.search))["selected"]
D = load(a.data, a.h3, include_test=True)
fit = np.where(D["split"] != "test")[0]; te = np.where(D["split"] == "test")[0]
P = D["P"][te]; tasks = D["task"][te]; sets = D["set"][te]
if sel["kind"] == "direct":
    mod = Direct().fit(D, fit)
else:
    mod = Ordinal(FEATS[sel["feature_set"]], sel["alpha"], sel["mix"]).fit(D, fit)
preds = {"FINAL_judge": mod.predict(D, te)}
cs = {s: marginal(D["C"][fit][D["set"][fit] == s]) for s in ("old", "new")}
preds["BASE_constant_per_set"] = np.array([cs[s] for s in sets])
preds["BASE_constant_pooled"] = np.tile(marginal(D["C"][fit]), (len(te), 1))
preds["BASE_uniform"] = np.full((len(te), 6), 1 / 6)
preds["BASE_H2_raw_astra_opus"] = D["H2raw"][te]
preds["BASE_edit_distance_calibrated"] = Ordinal(FEATS["F5_edit"], 1.0, 0.0).fit(D, fit).predict(D, te)
sol = D["H2sol_opus_raw"][te]
res = {"date": "11-24-2026", "selected": sel, "n_test_artifacts": int(len(te)), "n_test_tasks": int(len(set(tasks))), "subsets": {}}
M = {k: metrics_rows(P, Q) for k, Q in preds.items()}
for sub in ("pooled", "old", "new"):
    mask = np.ones(len(te), bool) if sub == "pooled" else sets == sub
    ix = np.where(mask)[0]

    def fn(idx, ix=ix):
        j = ix[idx]; o = {}
        for k in preds:
            for m in ("RPS", "CE", "TVD"):
                o[f"{k}|{m}"] = M[k][m][j].mean()
        for base in ("BASE_constant_per_set", "BASE_H2_raw_astra_opus"):
            for m in ("RPS", "CE", "TVD"):
                o[f"DIFF_FINAL_minus_{base}|{m}"] = M["FINAL_judge"][m][j].mean() - M[base][m][j].mean()
        return o

    # bootstrap over whole tasks inside the subset
    sub_tasks = tasks[ix]
    point, ci, _ = boot(sub_tasks, fn, a.draws)
    table = {}
    for k in preds:
        Qk = preds[k][ix]; sp, pe = corr(Qk, P[ix])
        table[k] = {m: {"point": float(point[f"{k}|{m}"]), "ci95": ci[f"{k}|{m}"]} for m in ("RPS", "CE", "TVD")}
        table[k].update(spearman=sp, pearson=pe)
    diffs = {k: {"point": float(point[k]), "ci95": ci[k]} for k in point if k.startswith("DIFF_")}
    res["subsets"][sub] = {"n_artifacts": int(len(ix)), "n_tasks": int(len(set(sub_tasks))), "metrics": table, "paired_differences": diffs}
if (sets == "old").any():
    ix = np.where(sets == "old")[0]
    res["old_only_H2_sol_plus_opus"] = {m: float(metrics_rows(P[ix], sol[ix])[m].mean()) for m in ("RPS", "CE", "TVD")}
pt = res["subsets"]["pooled"]
d_c = pt["paired_differences"]["DIFF_FINAL_minus_BASE_constant_per_set|RPS"]; d_h = pt["paired_differences"]["DIFF_FINAL_minus_BASE_H2_raw_astra_opus|RPS"]
ce_ok = pt["metrics"]["FINAL_judge"]["CE"]["point"] < pt["metrics"]["BASE_constant_per_set"]["CE"]["point"]
tvd_ok = pt["metrics"]["FINAL_judge"]["TVD"]["point"] < pt["metrics"]["BASE_constant_per_set"]["TVD"]["point"]
works = d_c["ci95"][1] < 0 and d_h["ci95"][1] < 0 and ce_ok and tvd_ok
promising = (d_c["point"] < 0 and d_h["point"] < 0 and ce_ok and tvd_ok)
res["verdict_per_PREREG"] = "works" if works else ("promising" if promising else "not found")
json.dump(res, open(a.out, "w"), indent=1)
for sub, v in res["subsets"].items():
    print("==", sub, v["n_tasks"], "tasks", v["n_artifacts"], "artifacts")
    for k, t in v["metrics"].items():
        print(f'{k:32s} RPS {t["RPS"]["point"]:.4f} [{t["RPS"]["ci95"][0]:.4f},{t["RPS"]["ci95"][1]:.4f}]  CE {t["CE"]["point"]:.3f}  TVD {t["TVD"]["point"]:.3f}  | rho {t["spearman"]:.2f} r {t["pearson"]:.2f}')
    for k, t in v["paired_differences"].items():
        print(f"  {k}: {t['point']:+.4f} [{t['ci95'][0]:+.4f},{t['ci95'][1]:+.4f}]")
print("VERDICT", res["verdict_per_PREREG"])
