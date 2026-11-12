#!/usr/bin/env python3
# TLDR: Experiment 110's VBV2 condition analysis: the pre-registered 15-criterion in-distribution test (CRITERIA_VBV2.md) of VeriBench V2 frontier-model candidates against the same 75-item human-rated pool, using experiment 110's own frozen functions; writes aggregate criterion statistics only (no FSC values). Zero model calls.
"""Run: python3 analyze_vbv2.py VBV2_FEATURES.jsonl OUT_DIR

VBV2_FEATURES.jsonl comes from gather_vbv2_on_snap.py (criterion numbers and hashes only; texts stay on SNAP).
Imports ../../scripts/analyze.py and extract_criteria.py unmodified (SHA-256 checked) and mirrors analyze.main()'s
nested analyse() step by step, so every verdict, interval and bootstrap uses the same code and seed as the VBV1 result.
"""
import collections
import gzip
import hashlib
import json
import os
import random
import sys
import time

import numpy as np
from scipy import stats

HERE = os.path.dirname(os.path.abspath(__file__))
E110 = os.path.dirname(os.path.dirname(HERE))
WT = os.path.dirname(os.path.dirname(E110))            # repository root of this checkout
sys.path.insert(0, os.path.join(E110, "scripts"))
import analyze as A                                    # noqa: E402  frozen experiment-110 analysis functions
import extract_criteria as ec                          # noqa: E402  frozen extractor

FROZEN = {"analyze.py": "d33b23b531c1877293a954a2ef9cf31c481a89faa33fb93391e6fd46bfd212c3",
          "extract_criteria.py": "d72481b87f0f7714574f2450cf08b42d502234e49c8ca1998c4657fabbf1daa1"}
sha = lambda p: hashlib.sha256(open(p, "rb").read()).hexdigest()
for name, mod in (("analyze.py", A), ("extract_criteria.py", ec)):
    assert sha(mod.__file__) == FROZEN[name], name + " is not the frozen experiment-110 version"

FEAT, OUT = sys.argv[1], sys.argv[2]
CRIT, A1_CRIT, JUDGE_CRIT = A.CRIT, A.A1_CRIT, A.JUDGE_CRIT
SEED, COVERAGE = A.SEED, A.COVERAGE
E100 = os.path.join(WT, "experiments/100_karpathy_recipe_tc_judge_search_human_train_val_test")
R110 = json.load(open(os.path.join(E110, "results/results.json")))
# experiment 103 VBV2 single-call condition: 7 served models x 5 full-source tasks (103 PROTOCOL, VBV2 section)
DECLARED_103 = {"gemini-3.1-pro-high", "gpt-5.6-luna-high", "gpt-5.6-sol-high", "claude-opus-5-max",
                "gpt-6-astra-high", "gpt-6-luna-high", "qwen3.6-27b-thinking"}
VBV2_TASKS = ["bst", "const_fold", "execute", "imp_compiler", "lower"]
t0 = time.time()

# ---------------- pool: committed experiment-110 features, with a seeded exact-reproduction check ----------------
pool = [json.loads(l) for l in gzip.open(os.path.join(E110, "results/features.jsonl.gz"), "rt") if '"POOL"' in l]
pool = [r for r in pool if r["cond"] == "POOL"]
assert len(pool) == 75, len(pool)
items = {it["item"]: it for it in (json.loads(l) for l in open(os.path.join(E100, "inputs/items.jsonl")))}
fix = lambda p: os.path.join(E100, p)  # items.jsonl paths are relative to experiment 100 (as in build_pool_manifest.py)
repro = []
for i in random.Random(20261009).sample(range(75), 3):
    r = pool[i]
    it = items[r["id"]]
    f = ec.features(A.rd(fix(it["candidate_path"])), A.rd(fix(it["ref_ann_path"])), A.rd(fix(it["py_ann_path"])))
    same = all(f.get(c) == r["f"].get(c) for c in A.FILE_CRIT + A1_CRIT)
    repro.append({"item": r["id"], "all_file_criteria_identical": same})
    assert same, ("pool row does not reproduce", r["id"], {c: (f.get(c), r["f"].get(c)) for c in A.FILE_CRIT if f.get(c) != r["f"].get(c)})
pool_clusters = [r["cluster"] for r in pool]
xpool = {c: A.vec(pool, c) for c in CRIT + A1_CRIT}
ks95, en95 = A.pool_null(xpool, pool_clusters, CRIT + A1_CRIT, np.random.default_rng(SEED))
null_check = {c: abs(ks95[c] - R110["pool_descriptive"][c]["ks_null95"]) < 1e-12 for c in CRIT}
assert all(null_check.values()), ("pool null differs from experiment 110", null_check)
err_rel = R110["error_relevance_on_pool"]
FEASIBLE = {"C5": (0, 1), "C6": (0, 1), "C7": (0, 1), "C8": (0, 3), "C10": (0, 1), "C11": (0, 1), "C12": (0, 1),
            "C11_A1": (0, 1), "C12_A1": (0, 1), "J1": (0, 5), "J2": (0, 5)}
vacuous = {c for c, (a, b) in FEASIBLE.items() if A.interval(xpool[c])[0] <= a and A.interval(xpool[c])[1] >= b}

# ---------------- VBV2 rows ----------------
rows = [json.loads(l) for l in open(FEAT)]
p7 = json.load(open(os.path.join(E100, "results/phase7/phase7_analysis.json")))
p7rep = {}
for cond in ("original", "rs"):
    for c in p7["conditions"][cond]["cells"]:
        p7rep[(cond, c["cell_id"])] = c.get("repeats") or {}
for r in rows:
    if r["source"].startswith("exp100_phase7"):
        name = r["cell_id"]
        if name.startswith("vbv2_multifile__"):
            r["model"], r["task"] = name.split("__", 1)[1], "E97-P001"
            r["cluster"] = "E97-P001"
        rep = p7rep.get((r["source"].split("phase7_")[1], name.replace("__", ":")), {})
        sol = [int(round(v * 5)) for v in rep.get("sol") or []]
        opu = [int(round(v * 5)) for v in rep.get("opus55") or []]
        if len(sol) == 3 and len(opu) == 3:
            r["f"]["J1"] = (max(sol) - min(sol) + max(opu) - min(opu)) / 2.0
            r["f"]["J2"] = abs(float(np.median(sol)) - float(np.median(opu)))
        r["is_fm"] = r["model"].lower() not in ("qwen", "qwen3.6-27b")


def analyse(name, rs, n_missing=0, do_boot=True):
    """Mirror of experiment 110 analyze.main().analyse (judge records available for every VBV2 source)."""
    y = {c: A.vec(rs, c) for c in CRIT + A1_CRIT}
    avail = {c: bool((~np.isnan(y[c])).sum()) for c in CRIT + A1_CRIT}
    per = {}
    for c in CRIT + A1_CRIT:
        if not avail[c]:
            per[c] = {"available": False, "why": "no computable values"}
            continue
        v = A.verdict(xpool[c], y[c])
        yy = y[c][~np.isnan(y[c])]
        xx = xpool[c][~np.isnan(xpool[c])]
        ksd = float(stats.ks_2samp(xx, yy).statistic)
        v.update({"available": True, "n_fm_values": int(len(yy)), "n_fm_nan": int(np.isnan(y[c]).sum()),
                  "ks_D": ksd, "ks_null95": ks95[c], "energy": float(stats.energy_distance(xx, yy)),
                  "energy_null95": en95[c]})
        v["ID_strict"] = bool(v["ID"] and ksd <= ks95[c])
        if n_missing:
            v["coverage_missing_as_outside"] = float(v["coverage"] * len(yy) / (len(yy) + n_missing))
        per[c] = v
    prim = [c for c in CRIT if avail[c]]
    alt = [("C11_A1" if c == "C11" else "C12_A1" if c == "C12" else c) for c in prim]
    out = {"n_files": len(rs), "n_missing_no_judged_candidate": n_missing, "n_tasks": len({r["cluster"] for r in rs}),
           "tasks": sorted({r["cluster"] for r in rs}), "models": sorted({r["model"] for r in rs}),
           "N": len(prim), "k": int(sum(per[c]["ID"] for c in prim)),
           "k_strict": int(sum(per[c]["ID_strict"] for c in prim)),
           "k_at_0.60": int(sum(per[c]["ID_at_0.60"] for c in prim)), "k_at_0.80": int(sum(per[c]["ID_at_0.80"] for c in prim)),
           "k_A1": int(sum(per[c]["ID"] for c in alt if per[c].get("available"))),
           "vacuous_criteria": sorted(c for c in prim if c in vacuous),
           "k_informative": int(sum(per[c]["ID"] for c in prim if c not in vacuous)),
           "N_informative": len([c for c in prim if c not in vacuous]),
           "out_of_distribution": [c for c in prim if not per[c]["ID"]],
           "ood_and_error_relevant": [c for c in prim if not per[c]["ID"] and err_rel.get(c, {}).get("error_relevant")],
           "criteria": per}
    if n_missing:
        out["k_missing_as_outside"] = int(sum(per[c]["location_ok"] and per[c].get("coverage_missing_as_outside", per[c]["coverage"]) >= COVERAGE for c in prim))
    k = out["k"]
    out["label"] = "mostly in-distribution" if k >= 12 else "partially in-distribution" if k >= 8 else "substantially shifted"
    if do_boot and out["n_tasks"] >= 2:
        fm_cl = [r["cluster"] for r in rs]
        for draws in (A.DRAWS_PREREG, A.DRAWS_REQUESTED):
            ids = A.bootstrap_k(xpool, pool_clusters, y, fm_cl, [c for c in CRIT + A1_CRIT if avail[c]], draws,
                                np.random.default_rng(SEED))
            out["bootstrap_%d" % draws] = A.summarize_boot(ids, CRIT, A1_CRIT, avail)
    print("%-62s k=%2d/%d  n=%3d tasks=%d  %.0fs" % (name, out["k"], out["N"], len(rs), out["n_tasks"], time.time() - t0), flush=True)
    return out


prim_rows = [r for r in rows if r["source"] in ("exp103_vbv2", "exp103_vbv2_agent96") and r["is_fm"]]
judged_fm_103 = {(r["model"], r["task"]) for r in rows if r["source"] == "exp103_vbv2" and r["is_fm"]}
missing_fm_103 = 5 * len(DECLARED_103 - {"qwen3.6-27b-thinking"}) - len(judged_fm_103)
conds = collections.OrderedDict()
conds["PRIMARY: pooled frontier models, exp 103 VBV2 (single call + Terminus 2 GPT-6 Luna)"] = (prim_rows, missing_fm_103)
for m in sorted(DECLARED_103):
    rs = [r for r in rows if r["source"] == "exp103_vbv2" and r["model"] == m]
    conds["exp 103 single call %s%s" % (m, "" if m != "qwen3.6-27b-thinking" else " (not FM, comparison)")] = (rs, 5 - len(rs))
conds["exp 103 Terminus 2 + GPT-6 Luna (exp 96 captures)"] = ([r for r in rows if r["source"] == "exp103_vbv2_agent96"], 0)
conds["exp 103 recovery_1 (separately labelled)"] = ([r for r in rows if r["source"] == "exp103_vbv2_recovery_1"], 0)
for cond in ("phase7_original", "phase7_rs"):
    conds["SECONDARY (amendment V-A1): pooled frontier models, exp 100 %s" % cond] = (
        [r for r in rows if r["source"] == "exp100_" + cond and r["is_fm"]], 0)
results = {"conditions": {}}
for name, (rs, miss) in conds.items():
    results["conditions"][name] = analyse(name, rs, miss, do_boot=len(rs) >= 3) if rs else {"n_files": 0, "n_missing_no_judged_candidate": miss}

results.update({
    "written": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "model_calls": 0,
    "inputs": {"vbv2_features_sha256": sha(FEAT), "analyze_py_sha256": FROZEN["analyze.py"],
               "extract_criteria_py_sha256": FROZEN["extract_criteria.py"],
               "analyze_vbv2_py_sha256": sha(os.path.abspath(__file__)),
               "criteria_vbv2_md_sha256": sha(os.path.join(os.path.dirname(HERE), "CRITERIA_VBV2.md")),
               "pool_features_sha256": sha(os.path.join(E110, "results/features.jsonl.gz"))},
    "data_checks": {"pool_rows": len(pool), "pool_reproduction": repro, "pool_null_matches_experiment_110": all(null_check.values()),
                    "vbv2_rows": len(rows), "by_source": dict(collections.Counter(r["source"] for r in rows)),
                    "j12_complete": dict(collections.Counter(r["source"] for r in rows if r["f"].get("J1") is not None)),
                    "main_function_unmatched_prereg": dict(collections.Counter(r["source"] for r in rows if not r["f"]["diag"]["lean_main_matched"])),
                    "exp103_fm_missing_no_judged_candidate": missing_fm_103,
                    "phase7_policy_rejected_or_prompt_confound": "flags not read (they sit beside FSC values); every phase-7 cell kept, reported separately"},
    "pool_descriptive": {c: R110["pool_descriptive"][c] for c in CRIT + A1_CRIT},
    "error_relevance_on_pool": {c: err_rel.get(c) for c in CRIT + A1_CRIT},
    "prediction": "pre-registered: pooled F2 k <= 7 (substantially shifted), with C1, C2, C3, C9 out of distribution",
    "runtime_seconds": round(time.time() - t0, 1)})
os.makedirs(OUT, exist_ok=True)
json.dump(results, open(os.path.join(OUT, "results_vbv2.json"), "w"), indent=1)
print("written", os.path.join(OUT, "results_vbv2.json"))
