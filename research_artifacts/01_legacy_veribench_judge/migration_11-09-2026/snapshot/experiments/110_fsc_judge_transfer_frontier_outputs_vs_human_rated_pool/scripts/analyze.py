# TLDR: Deterministic experiment-110 analysis: computes the 15 pre-registered criteria (CRITERIA.md) on the 75-item FSC judge-validation pool and on every frontier-model (FM) condition, applies the pre-declared in-distribution tests, reports k/N with task-cluster bootstrap intervals, and adds direct judge-side evidence; no model calls.
"""Run: python3 -I analyze.py   (from any directory; all paths absolute).

Outputs (scratchpad/x110/results/): features.jsonl, results.json, RESULTS.md.
"""
import collections
import hashlib
import json
import math
import os
import sys
import time

import numpy as np
from scipy import stats

X = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, X)
import extract_criteria as ec  # noqa: E402

REPO = "/Users/brandomiranda/veribench"
DS = REPO + "/veribench_dataset"
E100 = REPO + "/experiments/100_karpathy_recipe_tc_judge_search_human_train_val_test"
OUT = X + "/results"
SEED = 20261009
DRAWS_PREREG = 2000      # CRITERIA.md section 5
DRAWS_REQUESTED = 10000  # orchestrator request (10-09-2026); reported beside the pre-registered 2,000
NULL_SPLITS = 2000       # CRITERIA.md section 4
COVERAGE = 0.70
SENS = (0.60, 0.80)
FILE_CRIT = ["C1", "C2", "C3", "C4", "C5", "C6", "C7", "C8", "C9", "C10", "C11", "C12", "C13"]
JUDGE_CRIT = ["J1", "J2"]
CRIT = FILE_CRIT + JUDGE_CRIT
A1_CRIT = ["C11_A1", "C12_A1"]
CRIT_NAMES = {"C1": "File length (non-blank lines)", "C2": "Definitions", "C3": "Statement count",
              "C4": "Statement length (median tokens)", "C5": "Quantified statements (frac)",
              "C6": "Conditional/relational statements (frac)", "C7": "Ground-instance statements (frac)",
              "C8": "Pre/post scaffold (0-3)", "C9": "Executable tests", "C10": "Hole rate (sorry/admit)",
              "C11": "Main-function focus", "C12": "Lexical overlap with reference", "C13": "log2 statement-count ratio",
              "J1": "Judge repeat spread (raw 0-5)", "J2": "Judge member disagreement (raw 0-5)",
              "C11_A1": "Main-function focus (amendment A1)", "C12_A1": "Lexical overlap (amendment A1)"}
VBV1_N_TASKS = 896


def sha(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def rd(path):
    with open(path, encoding="utf-8", errors="replace") as fh:
        return fh.read()


# ---------------------------------------------------------------- live dataset index
def live_index():
    py = []
    for d, _, fs in os.walk(DS + "/py_src"):
        if "__pycache__" in d:
            continue
        py += [os.path.relpath(os.path.join(d, f), DS + "/py_src")[:-3] for f in fs if f.endswith(".py")]
    lean = []
    for d, _, fs in os.walk(DS + "/lean_src/veribench"):
        if ".lake" in d:
            continue
        lean += [os.path.relpath(os.path.join(d, f), DS + "/lean_src/veribench")[:-5] for f in fs if f.endswith(".lean")]

    def nk(p):
        return os.path.dirname(p) + "/" + os.path.basename(p).lower().replace("_", "")
    lean_by = {nk(l): l for l in lean}
    tasks = {}
    for p in py:
        tasks[p] = {"py": DS + "/py_src/" + p + ".py", "ref": DS + "/lean_src/veribench/" + lean_by[nk(p)] + ".lean",
                    "lean_rel": lean_by[nk(p)]}
    by_lean = {nk(v["lean_rel"]): k for k, v in tasks.items()}
    by_flat = {k.replace("/", "__").lower(): k for k in tasks}
    return tasks, by_lean, by_flat, nk


def strip_num(stem):
    import re
    return re.sub(r"^\d+_?", "", stem).lower().replace("_", "")


def map_pool_tasks(pool_items, tasks):
    """Map each pool (domain, task) to one live py task key; exact stem first, then number-stripped stem."""
    out = {}
    for it in pool_items:
        key = (it["domain"], it["task"])
        if key in out:
            continue
        cands = [k for k in tasks if k.split("/")[0] == it["domain"] and os.path.basename(k).lower() == it["task"].lower()]
        if len(cands) != 1:
            cands = [k for k in tasks if k.split("/")[0] == it["domain"] and strip_num(os.path.basename(k)) == strip_num(it["task"])]
        out[key] = cands[0] if len(cands) == 1 else None
    return out


# ---------------------------------------------------------------- records
def build_records():
    pool = json.load(open(X + "/pool_manifest.json"))
    fm = json.load(open(X + "/fm_manifest.json"))
    tasks, by_lean, by_flat, nk = live_index()
    pool_map = map_pool_tasks(pool["items"], tasks)
    pool_live = {v for v in pool_map.values() if v}
    recs = []
    for it in pool["items"]:
        sol = [round(float(v) * 5) for v in it["h2_sol_high"]["raw_repeats"]]
        opu = [round(float(v) * 5) for v in it["h2_opus55_max"]["raw_repeats"]]
        recs.append({"cond": "POOL", "cluster": it["task"], "id": it["item"], "split": it["split"],
                     "cand": it["candidate_path"], "ref": it["reference_rater_era_path"], "py": it["python_rater_era_path"],
                     "sol": sol, "opus": opu, "h2": round(float(it["h2_ensemble_0_1"]), 9),
                     "human": it["human_target_0_1"], "live_task": pool_map[(it["domain"], it["task"])],
                     "sha_expected": it["candidate_sha256"]})
    missing = collections.Counter()
    unmapped = collections.Counter()
    for it in fm["items"]:
        src = it["source"]
        if not src.startswith(("exp102", "exp103_vbv1", "exp107")):
            continue  # VBV2 (exp103_vbv2*, exp100_phase7*) out of scope for the primary claim (CRITERIA.md section 1)
        if src == "exp102_table2_rescore":
            cond = "exp102:" + it["system"]
            live = by_lean.get(nk(it["task"]))
        elif src.startswith("exp103_vbv1"):
            suffix = {"exp103_vbv1": "", "exp103_vbv1_agent95": "", "exp103_vbv1_recovery_1": "|recovery_1"}[src]
            cond = "exp103:" + it["system"] + suffix
            live = by_flat.get(it["task"].lower())
        else:
            cond = "exp107:" + ("setN_packet" if "setN" in src else "setB_packet")
            live = None
        lp = it["file"].get("local_path")
        if lp and not lp.startswith("/"):
            lp = REPO + "/" + lp
        j = it.get("judge") or {}
        reps = j.get("repeats_0_5") or {}
        rec = {"cond": cond, "id": src + "|" + (it.get("task") or it.get("packet_item") or ""), "source": src,
               "system": it["system"], "is_fm": it.get("is_frontier_model"), "cand": lp,
               "sha_expected": it["file"].get("sha256"), "live_task": live,
               "sol": reps.get("H2_sol_high"), "opus": reps.get("H2_opus55_max"),
               "h2": j.get("FSC_H2_recomputed_from_repeats"), "human": it.get("human_rating"),
               "status": j.get("status")}
        if src.startswith("exp107"):
            pdir = os.path.dirname(os.path.dirname(lp))
            g = os.listdir(pdir + "/gold_lean")
            p = os.listdir(pdir + "/python_source")
            rec["ref"] = pdir + "/gold_lean/" + g[0] if len(g) == 1 else None
            rec["py"] = pdir + "/python_source/" + p[0] if len(p) == 1 else None
            rec["cluster"] = os.path.basename(pdir)
            rec["sol"] = rec["opus"] = rec["h2"] = None  # SEALED: never read
        else:
            if live is None:
                unmapped[cond] += 1
            rec["ref"] = tasks[live]["ref"] if live else None
            rec["py"] = tasks[live]["py"] if live else None
            rec["cluster"] = live or it["task"]
        if not lp or not os.path.exists(lp) or j.get("status") == "zero_without_call":
            missing[cond] += 1
            rec["missing"] = True
        recs.append(rec)
    return recs, pool_map, pool_live, missing, unmapped


# ---------------------------------------------------------------- features
def compute_features(recs):
    sha_mismatch = []
    for r in recs:
        r["f"] = None
        if r.get("missing"):
            continue
        txt = rd(r["cand"])
        if r.get("sha_expected") and sha(r["cand"]) != r["sha_expected"]:
            sha_mismatch.append(r["id"])
        ref = rd(r["ref"]) if r.get("ref") else None
        py = rd(r["py"]) if r.get("py") else None
        f = ec.features(txt, ref, py)
        if r["sol"] and r["opus"] and len(r["sol"]) == 3 and len(r["opus"]) == 3:
            f["J1"] = (max(r["sol"]) - min(r["sol"]) + max(r["opus"]) - min(r["opus"])) / 2.0
            f["J2"] = abs(float(np.median(r["sol"])) - float(np.median(r["opus"])))
        else:
            f["J1"] = f["J2"] = None
        r["f"] = f
    return sha_mismatch


def vec(recs, crit):
    return np.array([np.nan if (r["f"] is None or r["f"].get(crit) is None) else float(r["f"][crit]) for r in recs])


# ---------------------------------------------------------------- tests
def interval(x):
    x = x[~np.isnan(x)]
    p5, p95 = np.quantile(x, [0.05, 0.95])  # numpy 'linear' = Hyndman-Fan type 7
    degenerate = bool(p5 == p95)
    if degenerate:
        return float(x.min()), float(x.max()), True, float(p5), float(p95)
    return float(p5), float(p95), False, float(p5), float(p95)


def verdict(x, y, thr=COVERAGE):
    y = y[~np.isnan(y)]
    if len(y) == 0 or np.isnan(x).all():
        return None
    lo, hi, deg, p5, p95 = interval(x)
    med = float(np.median(y))
    cov = float(np.mean((y >= lo) & (y <= hi)))
    return {"lo": lo, "hi": hi, "degenerate_pool_interval": deg, "pool_P5": p5, "pool_P95": p95,
            "fm_median": med, "fm_q25": float(np.quantile(y, 0.25)), "fm_q75": float(np.quantile(y, 0.75)),
            "fm_mean": float(np.mean(y)), "coverage": cov, "location_ok": lo <= med <= hi,
            "ID": bool(lo <= med <= hi and cov >= thr),
            "ID_at_0.60": bool(lo <= med <= hi and cov >= 0.60), "ID_at_0.80": bool(lo <= med <= hi and cov >= 0.80)}


def pool_null(xpool, clusters, crits, rng):
    """Pool-internal null: NULL_SPLITS random 12/13 task splits; KS D and energy distance between halves."""
    tasks = sorted(set(clusters))
    cl = np.array(clusters)
    ks = {c: [] for c in crits}
    en = {c: [] for c in crits}
    for _ in range(NULL_SPLITS):
        perm = rng.permutation(len(tasks))
        a = set(tasks[i] for i in perm[:12])
        ma = np.array([c in a for c in cl])
        for c in crits:
            x = xpool[c]
            xa, xb = x[ma & ~np.isnan(x)], x[~ma & ~np.isnan(x)]
            if len(xa) and len(xb):
                ks[c].append(stats.ks_2samp(xa, xb).statistic)
                en[c].append(stats.energy_distance(xa, xb))
    return ({c: float(np.quantile(ks[c], 0.95)) if ks[c] else None for c in crits},
            {c: float(np.quantile(en[c], 0.95)) if en[c] else None for c in crits})


def bootstrap_k(xpool, pool_clusters, yfm, fm_clusters, crits, draws, rng, chunk=500):
    """Task-cluster bootstrap of each criterion's primary verdict: pool tasks and FM tasks resampled independently."""
    ptasks = sorted(set(pool_clusters))
    pidx = {t: [i for i, c in enumerate(pool_clusters) if c == t] for t in ptasks}
    sizes = {len(v) for v in pidx.values()}
    assert sizes == {3}, sizes
    pmat = np.array([pidx[t] for t in ptasks])  # 25 x 3
    ftasks = sorted(set(fm_clusters))
    fti = {t: i for i, t in enumerate(ftasks)}
    ftask_of = np.array([fti[c] for c in fm_clusters])
    nt = len(ftasks)
    ids = {c: np.zeros(draws, dtype=bool) for c in crits}
    done = 0
    while done < draws:
        b = min(chunk, draws - done)
        ps = rng.integers(0, len(ptasks), size=(b, len(ptasks)))
        items = pmat[ps].reshape(b, -1)  # b x 75
        counts = rng.multinomial(nt, np.full(nt, 1.0 / nt), size=b)  # b x nt
        for c in crits:
            xs = xpool[c][items]  # b x 75
            with np.errstate(all="ignore"):
                p5 = np.nanquantile(xs, 0.05, axis=1)
                p95 = np.nanquantile(xs, 0.95, axis=1)
                mn = np.nanmin(xs, axis=1)
                mx = np.nanmax(xs, axis=1)
            deg = p5 == p95
            lo = np.where(deg, mn, p5)
            hi = np.where(deg, mx, p95)
            y = yfm[c]
            ok = ~np.isnan(y)
            if ok.sum() == 0:
                continue
            yv = y[ok]
            o = np.argsort(yv, kind="stable")
            ys = yv[o]
            W = counts[:, ftask_of[ok][o]].astype(np.float64)  # b x n
            cum = np.cumsum(W, axis=1)
            N = cum[:, -1]
            pos_lo = np.where(N % 2 == 1, (N - 1) / 2, N / 2 - 1)
            pos_hi = np.where(N % 2 == 1, (N - 1) / 2, N / 2)
            i_lo = (cum > pos_lo[:, None]).argmax(axis=1)
            i_hi = (cum > pos_hi[:, None]).argmax(axis=1)
            med = (ys[i_lo] + ys[i_hi]) / 2
            inside = (ys[None, :] >= lo[:, None]) & (ys[None, :] <= hi[:, None])
            with np.errstate(all="ignore"):
                cov = (W * inside).sum(axis=1) / N
            ids[c][done:done + b] = (N > 0) & (med >= lo) & (med <= hi) & (cov >= COVERAGE)
        done += b
    return ids


def summarize_boot(ids, crits_primary, crits_a1, avail):
    use = [c for c in crits_primary if avail.get(c)]
    k = np.sum([ids[c] for c in use], axis=0) if use else np.zeros(1)
    alt = [("C11_A1" if c == "C11" else "C12_A1" if c == "C12" else c) for c in use]
    ka1 = np.sum([ids[c] for c in alt], axis=0) if use else np.zeros(1)
    return {"k_ci95": [float(np.quantile(k, 0.025)), float(np.quantile(k, 0.975))], "k_boot_median": float(np.median(k)),
            "k_A1_ci95": [float(np.quantile(ka1, 0.025)), float(np.quantile(ka1, 0.975))],
            "stability": {c: float(np.mean(ids[c])) for c in list(crits_primary) + list(crits_a1) if c in ids and avail.get(c, True)}}


# ---------------------------------------------------------------- agreement metrics
def icc_a1(a, b):
    Y = np.column_stack([a, b])
    n, k = Y.shape
    gm = Y.mean()
    msr = k * ((Y.mean(axis=1) - gm) ** 2).sum() / (n - 1)
    msc = n * ((Y.mean(axis=0) - gm) ** 2).sum() / (k - 1)
    sse = ((Y - Y.mean(axis=1, keepdims=True) - Y.mean(axis=0, keepdims=True) + gm) ** 2).sum()
    mse = sse / ((n - 1) * (k - 1))
    return float((msr - mse) / (msr + (k - 1) * mse + k / n * (msc - mse)))


def agreement(j, h):
    j, h = np.asarray(j, float), np.asarray(h, float)
    return {"n_items": int(len(j)), "spearman": float(stats.spearmanr(j, h).statistic),
            "kendall_tau_b": float(stats.kendalltau(j, h).statistic), "pearson": float(stats.pearsonr(j, h).statistic),
            "icc_A1": icc_a1(j, h), "mae": float(np.mean(np.abs(j - h))), "mean_judge": float(j.mean()),
            "mean_human": float(h.mean()), "mean_bias_judge_minus_human": float((j - h).mean())}


def cluster_boot_stat(groups, fn, draws, rng):
    """groups: list of per-task lists of row indices; fn(rows)->float. Percentile 95% interval."""
    out = []
    G = len(groups)
    for _ in range(draws):
        rows = [i for g in rng.integers(0, G, G) for i in groups[g]]
        v = fn(rows)
        if v is not None and not np.isnan(v):
            out.append(v)
    return [float(np.quantile(out, 0.025)), float(np.quantile(out, 0.975))] if out else None, len(out)


# ---------------------------------------------------------------- main
def main():
    t0 = time.time()
    os.makedirs(OUT, exist_ok=True)
    recs, pool_map, pool_live, missing, unmapped = build_records()
    sha_mismatch = compute_features(recs)
    with open(OUT + "/features.jsonl", "w") as fh:
        for r in recs:
            fh.write(json.dumps({k: r.get(k) for k in ("cond", "id", "cluster", "live_task", "cand", "missing", "f")}, ensure_ascii=False) + "\n")
    pool = [r for r in recs if r["cond"] == "POOL"]
    pool_clusters = [r["cluster"] for r in pool]
    xpool = {c: vec(pool, c) for c in CRIT + A1_CRIT}

    by_cond = collections.defaultdict(list)
    for r in recs:
        if r["cond"] != "POOL":
            by_cond[r["cond"]].append(r)
    fm_conds_primary = ["exp102:claude_code", "exp102:codex", "exp102:baseline",
                        "exp103:single_call:claude-opus-5-max", "exp103:single_call:gemini-3.1-pro-high",
                        "exp103:single_call:gpt-5.6-luna-high", "exp103:single_call:gpt-5.6-sol-high",
                        "exp103:single_call:gpt-6-astra-high", "exp103:single_call:gpt-6-luna-high",
                        "exp103:agent:gpt-6-luna-high"]
    nonfm = ["exp102:leanstral", "exp103:single_call:qwen3.6-27b-thinking"]
    separate = sorted(c for c in by_cond if c.endswith("|recovery_1")) + ["exp107:setN_packet", "exp107:setB_packet"]
    labels = {"exp102:claude_code": "Claude Code + Claude Opus 5 (exp 102 Table 2)",
              "exp102:codex": "Codex + GPT-5.6 Sol (exp 102 Table 2)",
              "exp102:baseline": "Single-call Claude Opus 5 baseline (exp 102 Table 2)",
              "exp102:leanstral": "Leanstral (exp 102 Table 2; not FM)",
              "exp103:agent:gpt-6-luna-high": "Terminus 2 + GPT-6 Luna high (exp 95 bytes, exp 103 judge)",
              "exp107:setN_packet": "exp 107 set-N packet (blinded; 4 FM agents + Kimi K3; judge SEALED)",
              "exp107:setB_packet": "exp 107 set-B packet (blinded; Fable 5.1, Astra, Qwen; judge SEALED)"}

    def label(c):
        return labels.get(c, c.replace("exp103:", "").replace("single_call:", "single call ") + " (exp 103)")

    # Conditions to analyse: (name, records, judge_available)
    conds = []
    pooled = [r for c in fm_conds_primary for r in by_cond[c]]
    conds.append(("POOLED_FM (deployed set)", pooled, True))
    for c in fm_conds_primary + nonfm + separate:
        conds.append((c, by_cond[c], not c.startswith("exp107")))
    matched = [("POOLED_FM matched to the 25 pool tasks", [r for r in pooled if r["live_task"] in pool_live], True)]
    for c in fm_conds_primary:
        matched.append((c + " [matched]", [r for r in by_cond[c] if r["live_task"] in pool_live], True))

    rng_null = np.random.default_rng(SEED)
    ks95, en95 = pool_null(xpool, pool_clusters, CRIT + A1_CRIT, rng_null)

    # Section 6: error relevance on the pool (judge error = H2 ensemble - human, both 0-1)
    err = np.array([r["h2"] - r["human"] for r in pool])
    groups = [[i for i, r in enumerate(pool) if r["cluster"] == t] for t in sorted(set(pool_clusters))]
    rng6 = np.random.default_rng(SEED)
    err_rel = {}
    G = len(groups)
    gm = np.array(groups)
    boots = rng6.integers(0, G, size=(DRAWS_REQUESTED, G))
    rows_b = gm[boots].reshape(DRAWS_REQUESTED, -1)
    for c in CRIT + A1_CRIT:
        x = xpool[c]
        ok = ~np.isnan(x)
        if ok.sum() < 3 or np.nanstd(x) == 0:
            err_rel[c] = {"rho": None, "note": "constant or unavailable on pool"}
            continue
        rho = float(stats.spearmanr(x[ok], err[ok]).statistic)
        xb, eb = x[rows_b], err[rows_b]
        rx = stats.rankdata(xb, axis=1)
        re_ = stats.rankdata(eb, axis=1)
        rx = rx - rx.mean(1, keepdims=True)
        re_ = re_ - re_.mean(1, keepdims=True)
        with np.errstate(all="ignore"):
            rb = (rx * re_).sum(1) / np.sqrt((rx ** 2).sum(1) * (re_ ** 2).sum(1))
        rb = rb[~np.isnan(rb)]
        lo, hi = float(np.quantile(rb, 0.025)), float(np.quantile(rb, 0.975))
        err_rel[c] = {"rho": rho, "ci95": [lo, hi], "draws_used": int(len(rb)),
                      "error_relevant": bool(abs(rho) >= 0.30 and (lo > 0 or hi < 0))}

    results = {"conditions": {}, "matched": {}}

    def unlisted(rs):
        """exp 103 manifests list only tasks with an output file; the rest of the 896 VBV1 tasks are missing outputs."""
        n = 0
        for c in {r["cond"] for r in rs}:
            if c.startswith("exp103:") and not c.endswith("|recovery_1"):
                n += VBV1_N_TASKS - len(by_cond[c])
        return n

    def unlisted_matched(rs):
        """VERIFY FIX (10-09-2026): exp 103 matched-task rows also miss the pool tasks a model has no output for."""
        n = 0
        for c in {r["cond"] for r in rs}:
            if c.startswith("exp103:") and not c.endswith("|recovery_1"):
                n += len(pool_live) - len({r["live_task"] for r in by_cond[c] if r["live_task"] in pool_live})
        return n

    # VERIFY ADDITION: a criterion is vacuous when the pool interval already spans its whole feasible range,
    # so no FM set can fail it; k_informative counts ID criteria excluding those.
    FEASIBLE = {"C5": (0, 1), "C6": (0, 1), "C7": (0, 1), "C8": (0, 3), "C10": (0, 1), "C11": (0, 1), "C12": (0, 1),
                "C11_A1": (0, 1), "C12_A1": (0, 1), "J1": (0, 5), "J2": (0, 5)}
    vacuous = set()
    for c, (a, b) in FEASIBLE.items():
        lo_, hi_, _, _, _ = interval(xpool[c])
        if lo_ <= a and hi_ >= b:
            vacuous.add(c)

    def analyse(name, rs, judge_ok, do_boot=True):
        present = [r for r in rs if not r.get("missing")]
        extra_missing = unlisted_matched(rs) if "matched" in name else unlisted(rs)
        y = {c: vec(present, c) for c in CRIT + A1_CRIT}
        avail = {}
        why = {}
        for c in CRIT + A1_CRIT:
            n_ok = int((~np.isnan(y[c])).sum())
            if c in JUDGE_CRIT and not judge_ok:
                avail[c], why[c] = False, "judge records SEALED (exp 107 protocol amendments 4/10/11); not read"
            elif n_ok == 0:
                avail[c], why[c] = False, "no computable values"
            else:
                avail[c] = True
        per = {}
        for c in CRIT + A1_CRIT:
            if not avail[c]:
                per[c] = {"available": False, "why": why[c]}
                continue
            v = verdict(xpool[c], y[c])
            yy = y[c][~np.isnan(y[c])]
            xx = xpool[c][~np.isnan(xpool[c])]
            ksd = float(stats.ks_2samp(xx, yy).statistic)
            v.update({"available": True, "n_fm_values": int(len(yy)), "n_fm_nan": int(np.isnan(y[c]).sum()),
                      "ks_D": ksd, "ks_null95": ks95[c], "energy": float(stats.energy_distance(xx, yy)),
                      "energy_null95": en95[c]})
            v["ID_strict"] = bool(v["ID"] and ksd <= ks95[c])
            n_missing = len(rs) - len(present) + extra_missing
            if n_missing:
                v["coverage_missing_as_outside"] = float(v["coverage"] * len(yy) / (len(yy) + n_missing))
            per[c] = v
        prim = [c for c in CRIT if avail[c]]
        k = sum(per[c]["ID"] for c in prim)
        alt = [("C11_A1" if c == "C11" else "C12_A1" if c == "C12" else c) for c in prim]
        out = {"label": label(name.split(" [")[0]) if not name.startswith("POOLED") else name,
               "n_records": len(rs), "n_files_present": len(present), "n_missing_or_no_output": len(rs) - len(present) + extra_missing,
               "n_tasks": len({r["cluster"] for r in present}),
               "N": len(prim), "k": int(k), "k_strict": int(sum(per[c]["ID_strict"] for c in prim)),
               "k_at_0.60": int(sum(per[c]["ID_at_0.60"] for c in prim)), "k_at_0.80": int(sum(per[c]["ID_at_0.80"] for c in prim)),
               "k_A1": int(sum(per[c]["ID"] for c in alt if per[c].get("available"))),
               "vacuous_criteria": sorted(c for c in prim if c in vacuous),
               "k_informative": int(sum(per[c]["ID"] for c in prim if c not in vacuous)),
               "N_informative": len([c for c in prim if c not in vacuous]),
               "out_of_distribution": [c for c in prim if not per[c]["ID"]],
               "ood_and_error_relevant": [c for c in prim if not per[c]["ID"] and err_rel.get(c, {}).get("error_relevant")],
               "criteria": per}
        if any(r.get("missing") for r in rs) or extra_missing:
            out["k_missing_as_outside"] = int(sum(per[c]["location_ok"] and per[c].get("coverage_missing_as_outside", per[c]["coverage"]) >= COVERAGE for c in prim))
        if do_boot and len({r["cluster"] for r in present}) >= 2:
            fm_cl = [r["cluster"] for r in present]
            for draws in (DRAWS_PREREG, DRAWS_REQUESTED):
                ids = bootstrap_k(xpool, pool_clusters, y, fm_cl, [c for c in CRIT + A1_CRIT if avail[c]], draws,
                                  np.random.default_rng(SEED))
                out["bootstrap_%d" % draws] = summarize_boot(ids, CRIT, A1_CRIT, avail)
        return out

    for name, rs, jok in conds:
        results["conditions"][name] = analyse(name, rs, jok)
        print("%-55s k=%s/%s  %.0fs" % (name, results["conditions"][name]["k"], results["conditions"][name]["N"], time.time() - t0), flush=True)
    for name, rs, jok in matched:
        results["matched"][name] = analyse(name, rs, jok)
        print("%-55s k=%s/%s  %.0fs" % (name, results["matched"][name]["k"], results["matched"][name]["N"], time.time() - t0), flush=True)

    # Pool descriptive per criterion
    pool_desc = {}
    for c in CRIT + A1_CRIT:
        lo, hi, deg, p5, p95 = interval(xpool[c])
        pool_desc[c] = {"name": CRIT_NAMES[c], "median": float(np.nanmedian(xpool[c])), "P5": p5, "P95": p95,
                        "interval_used": [lo, hi], "degenerate": deg, "n": int((~np.isnan(xpool[c])).sum()),
                        "ks_null95": ks95[c], "energy_null95": en95[c]}

    # ---------------- direct evidence
    # (a) judge--human agreement on human-rated FM items
    fm_rated = [r for r in recs if r["cond"] != "POOL" and r.get("human") is not None and r.get("h2") is not None]
    direct_a = {"n_items": len(fm_rated), "available": bool(fm_rated),
                "why": "No human ratings of FM outputs exist as of 10-09-2026 (exp 108 pilot 0/2 filled and practice-only; "
                       "exp 102 set N 0 sheets returned, round closes 11-06-2026; sets A/B 0 sheets)." if not fm_rated else None}
    # pool agreement recomputed (check against receipts) and copied receipts
    agree_recomputed = {}
    for sp in ("train", "validation", "test", "all"):
        rows = [r for r in pool if sp == "all" or r["split"] == {"validation": "val"}.get(sp, sp) or r["split"] == sp]
        if not rows:
            continue
        a = agreement([r["h2"] for r in rows], [r["human"] for r in rows])
        g = collections.defaultdict(list)
        for i, r in enumerate(rows):
            g[r["cluster"]].append(i)
        gl = list(g.values())
        jj = np.array([r["h2"] for r in rows])
        hh = np.array([r["human"] for r in rows])
        rng_a = np.random.default_rng(SEED)
        for m, fn in (("spearman", lambda ix: stats.spearmanr(jj[ix], hh[ix]).statistic),
                      ("pearson", lambda ix: stats.pearsonr(jj[ix], hh[ix]).statistic if np.std(jj[ix]) > 0 and np.std(hh[ix]) > 0 else np.nan),
                      ("kendall_tau_b", lambda ix: stats.kendalltau(jj[ix], hh[ix]).statistic),
                      ("icc_A1", lambda ix: icc_a1(jj[ix], hh[ix])),
                      ("mae", lambda ix: float(np.mean(np.abs(jj[ix] - hh[ix])))),
                      ("mean_bias_judge_minus_human", lambda ix: float(np.mean(jj[ix] - hh[ix])))):
            ci, used = cluster_boot_stat(gl, fn, DRAWS_REQUESTED, rng_a)
            a[m + "_ci95"] = ci
            a[m + "_draws_used"] = used
        a["n_tasks"] = len(gl)
        agree_recomputed[sp] = a
    receipts = {}
    for sp, fn in (("train", "train"), ("validation", "val"), ("test", "test")):
        d = json.load(open(E100 + "/results/ensembles/%s_H2_sol_plus_H2_opus.json" % fn))
        a = d["agreement"]
        receipts[sp] = {k: a[k] for k in ("n_items", "n_tasks", "spearman", "kendall_tau_b", "pearson", "icc_A1", "mae", "mean_pred", "mean_target") if k in a}
        receipts[sp]["mean_bias_judge_minus_human"] = a["mean_pred"] - a["mean_target"]
        receipts[sp]["stability"] = d["stability_per_pass_mean"]
    tr = json.load(open(E100 + "/results/TEST_RECEIPT.json"))
    receipts["test"]["bootstrap_ci95"] = {m: [tr["all_items"]["bootstrap"][m]["lo"], tr["all_items"]["bootstrap"][m]["hi"]] for m in tr["all_items"]["bootstrap"]}
    receipts["validation"]["tie_fix_note"] = "exp 102 REPORT.md finding 1: with predictions rounded to 1e-9, validation Spearman 0.880 and Kendall 0.823 (receipt file: 0.870, 0.792); all-75 Spearman 0.758."

    # (b) repeat SD and member disagreement, (c) score distribution shift
    def judge_stats(rs):
        rs = [r for r in rs if r.get("sol") and r.get("opus") and not r.get("missing") and len(r["sol"]) == 3 and len(r["opus"]) == 3]
        if not rs:
            return None
        sd_sol = np.array([np.std(np.array(r["sol"]) / 5, ddof=1) for r in rs])
        sd_opu = np.array([np.std(np.array(r["opus"]) / 5, ddof=1) for r in rs])
        dis = np.array([abs(np.median(r["sol"]) - np.median(r["opus"])) / 5 for r in rs])
        h2 = np.array([r["h2"] for r in rs], float)
        return {"n": len(rs), "n_tasks": len({r["cluster"] for r in rs}),
                "mean_repeat_sd_sol_0_1": float(sd_sol.mean()), "mean_repeat_sd_opus_0_1": float(sd_opu.mean()),
                "mean_repeat_sd_both_0_1": float((sd_sol.mean() + sd_opu.mean()) / 2),
                "p90_repeat_sd_both_0_1": float(np.quantile(np.concatenate([sd_sol, sd_opu]), 0.90)),
                "frac_items_any_repeat_change": float(np.mean((sd_sol > 0) | (sd_opu > 0))),
                "mean_member_disagreement_0_1": float(dis.mean()), "frac_members_disagree": float(np.mean(dis > 0)),
                "frac_member_disagree_ge_0.4": float(np.mean(dis >= 0.4 - 1e-9)),
                "h2_mean": float(h2.mean()), "h2_median": float(np.median(h2)), "h2_frac_eq_1": float(np.mean(h2 >= 1 - 1e-9)),
                "h2_frac_ge_0.9": float(np.mean(h2 >= 0.9 - 1e-9)), "h2_q10_q90": [float(np.quantile(h2, 0.1)), float(np.quantile(h2, 0.9))],
                "_h2": h2, "_sd": (sd_sol + sd_opu) / 2, "_dis": dis, "_cl": [r["cluster"] for r in rs]}

    pj = judge_stats(pool)
    h2_lo, h2_hi, _, _, _ = interval(pj["_h2"])
    # h2 null for KS
    tasks_sorted = sorted(set(pool_clusters))
    rng_h = np.random.default_rng(SEED)
    ksn, enn = [], []
    cl = np.array(pj["_cl"])
    for _ in range(NULL_SPLITS):
        a = set(tasks_sorted[i] for i in rng_h.permutation(len(tasks_sorted))[:12])
        m = np.array([c in a for c in cl])
        ksn.append(stats.ks_2samp(pj["_h2"][m], pj["_h2"][~m]).statistic)
        enn.append(stats.energy_distance(pj["_h2"][m], pj["_h2"][~m]))
    h2_ks95, h2_en95 = float(np.quantile(ksn, 0.95)), float(np.quantile(enn, 0.95))

    def diff_ci(a_vals, a_cl, b_vals, b_cl, draws, seed):
        rng = np.random.default_rng(seed)
        def groups_of(vals, cls):
            g = collections.defaultdict(list)
            for v, c in zip(vals, cls):
                g[c].append(v)
            return [np.array(v) for v in g.values()]
        ga, gb = groups_of(a_vals, a_cl), groups_of(b_vals, b_cl)
        sa = np.array([g.sum() for g in ga]); na = np.array([len(g) for g in ga])
        sb = np.array([g.sum() for g in gb]); nb = np.array([len(g) for g in gb])
        ca = rng.multinomial(len(ga), np.full(len(ga), 1 / len(ga)), size=draws)
        cb = rng.multinomial(len(gb), np.full(len(gb), 1 / len(gb)), size=draws)
        d = (cb @ sb) / (cb @ nb) - (ca @ sa) / (ca @ na)
        return [float(np.quantile(d, 0.025)), float(np.quantile(d, 0.975))]

    judge_side = {"POOL": {k: v for k, v in pj.items() if not k.startswith("_")}}
    for name, rs, jok in conds + matched:
        if not jok:
            judge_side[name] = {"available": False, "why": "exp 107 judge values SEALED; not read"}
            continue
        s = judge_stats(rs)
        if s is None:
            judge_side[name] = {"available": False, "why": "no judge records"}
            continue
        s["h2_ks_D_vs_pool"] = float(stats.ks_2samp(pj["_h2"], s["_h2"]).statistic)
        s["h2_ks_null95"] = h2_ks95
        s["h2_energy_vs_pool"] = float(stats.energy_distance(pj["_h2"], s["_h2"]))
        s["h2_energy_null95"] = h2_en95
        s["h2_frac_in_pool_P5_P95"] = float(np.mean((s["_h2"] >= h2_lo) & (s["_h2"] <= h2_hi)))
        s["h2_pool_P5_P95"] = [h2_lo, h2_hi]
        s["diff_h2_mean_vs_pool_ci95"] = diff_ci(pj["_h2"], pj["_cl"], s["_h2"], s["_cl"], DRAWS_REQUESTED, SEED)
        s["diff_repeat_sd_vs_pool_ci95"] = diff_ci(pj["_sd"], pj["_cl"], s["_sd"], s["_cl"], DRAWS_REQUESTED, SEED)
        s["diff_member_disagreement_vs_pool_ci95"] = diff_ci(pj["_dis"], pj["_cl"], s["_dis"], s["_cl"], DRAWS_REQUESTED, SEED)
        judge_side[name] = {k: v for k, v in s.items() if not k.startswith("_")}

    # diagnostics
    def diag(rs):
        fs = [r["f"]["diag"] for r in rs if r.get("f")]
        if not fs:
            return None
        def m(key, fn=np.mean):
            v = [d[key] for d in fs if d.get(key) is not None]
            return float(fn(v)) if v else None
        ic = [r for r in rs if False]
        return {"n": len(fs), "comment_density_median": m("comment_density", np.median), "snake_case_def_frac_mean": m("snake_case_def_frac"),
                "decidable_typeclass_structure_mean": m("decidable_typeclass_structure"), "native_decide_mean": m("native_decide"),
                "mathlib_import_frac": m("mathlib_import"), "lean_main_matched_frac": m("lean_main_matched"),
                "lean_main_matched_A1_frac": m("lean_main_matched_A1"), "py_main_is_pre_helper_frac":
                    float(np.mean([str(d.get("py_main", "")).lower().replace("_", "") in ec.A1_SKIP or str(d.get("py_main", "")).lower().startswith(("pre_", "post_")) for d in fs])),
                "ref_has_no_statements_frac": float(np.mean([d.get("n_ref_statements") in (0, None) for d in fs]))}
    diagnostics = {"POOL": diag(pool)}
    for name, rs, _ in conds:
        diagnostics[name] = diag(rs)

    results.update({
        "written": "10-09-2026", "model_calls": 0,
        "inputs": {"pool_manifest_sha256": sha(X + "/pool_manifest.json"), "fm_manifest_sha256": sha(X + "/fm_manifest.json"),
                   "criteria_md_sha256": sha(X + "/CRITERIA.md"), "extract_criteria_py_sha256": sha(X + "/extract_criteria.py"),
                   "analyze_py_sha256": sha(os.path.abspath(__file__))},
        "settings": {"seed": SEED, "coverage_threshold": COVERAGE, "sensitivity": SENS, "null_splits": NULL_SPLITS,
                     "bootstrap_draws_preregistered": DRAWS_PREREG, "bootstrap_draws_requested": DRAWS_REQUESTED,
                     "quantile_type": "Hyndman-Fan type 7 (numpy linear)",
                     "pool_reference": "annotation-era reference and Python (what the H2 judge prompt contained: prompts.render reference='annotation')",
                     "fm_reference": "live veribench_dataset lean_src/py_src (exp 102/103); packet gold_lean/python_source (exp 107)",
                     "J1_J2_identity": "exp 102: protocol A3 equivalence gate, prompt SHA-256 120/120 per member (results/equivalence_gate.json); exp 103: prompt SHA-256 80/80 and oracle/blank controls PASS (results.md); exp 107: SEALED -> unavailable",
                     "vbv2": "exp 103 VBV2 and exp 100 phase 7 cells excluded (out of scope for the primary claim; files not local)",
                     "extractor_interpretation": ec.INTERPRETATION},
        "data_checks": {"candidate_sha_mismatches": sha_mismatch, "missing_by_condition": dict(missing),
                        "unmapped_task_by_condition": dict(unmapped),
                        "pool_task_to_live_task": {"%s/%s" % k: v for k, v in pool_map.items()},
                        "pool_tasks_mapped": sum(1 for v in pool_map.values() if v),
                        "vbv1_task_denominator": VBV1_N_TASKS,
                        "exp103_records_listed": {c: len(by_cond[c]) for c in by_cond if c.startswith("exp103")}},
        "pool_descriptive": pool_desc, "error_relevance_on_pool": err_rel,
        "direct_evidence": {"a_judge_human_agreement_on_FM": direct_a,
                            "a_reference_pool_agreement_receipts_exp100": receipts,
                            "a_reference_pool_agreement_recomputed_tiefixed": agree_recomputed,
                            "b_c_judge_side": judge_side},
        "diagnostics": diagnostics,
        "runtime_seconds": round(time.time() - t0, 1)})
    with open(OUT + "/results.json", "w") as fh:
        json.dump(results, fh, indent=1, default=lambda o: o.item() if hasattr(o, "item") else str(o))
    write_md(results)
    print("done %.0fs" % (time.time() - t0))


def f3(v, d=3):
    if v is None:
        return "n/a"
    if isinstance(v, bool):
        return "yes" if v else "no"
    if isinstance(v, (int,)) and not isinstance(v, bool):
        return str(v)
    return ("%." + str(d) + "f") % v


def write_md(R):
    L = []
    L.append("<!-- TLDR: Experiment 110 results: how many of the 15 pre-registered criteria place frontier-model (FM) Lean outputs inside the 75-item FSC judge-validation pool, per FM condition, with task-bootstrap intervals and direct judge-side evidence; generated by analyze.py, no model calls. -->")
    L.append("")
    L.append("# Experiment 110 results: frontier-model outputs vs the FSC judge-validation pool")
    L.append("")
    L.append("Generated 10-09-2026 by `analyze.py` (zero model calls). Pre-registration: `CRITERIA.md` (sha256 `%s`); extractor sha256 `%s`." % (R["inputs"]["criteria_md_sha256"][:16], R["inputs"]["extract_criteria_py_sha256"][:16]))
    L.append("Pool = 75 human-rated items (25 VBV1 tasks x 3 Claude 3.7 Sonnet outputs, train + validation + test). Rule: ID iff FM median in pool [P5, P95] and >= 0.70 of FM files inside (degenerate pool interval -> [min, max]). Strict = ID and KS D <= pool-internal null 95th percentile (2,000 task splits). Bootstrap: task-cluster, pool and FM tasks resampled independently; 2,000 draws pre-registered, 10,000 requested; seed 20261009.")
    L.append("")
    L.append("## Headline: k/N criteria in-distribution")
    L.append("")
    L.append("| Condition | Files (missing) | Tasks | k/N | 95% CI (10k) | 95% CI (2k, pre-reg) | strict | k @0.60 / @0.80 | k with A1 | out of distribution | OOD and error-relevant |")
    L.append("|---|---|---|---|---|---|---|---|---|---|---|")
    for sec in ("conditions", "matched"):
        for name, c in R[sec].items():
            b10 = c.get("bootstrap_10000", {}).get("k_ci95")
            b2 = c.get("bootstrap_2000", {}).get("k_ci95")
            L.append("| %s | %d (%d) | %d | **%d/%d** | %s | %s | %d | %d / %d | %d | %s | %s |" % (
                c["label"] + (" [matched]" if sec == "matched" and "matched" not in c["label"] else ""), c["n_files_present"], c["n_missing_or_no_output"], c["n_tasks"],
                c["k"], c["N"], ("%g-%g" % tuple(b10)) if b10 else "n/a", ("%g-%g" % tuple(b2)) if b2 else "n/a",
                c["k_strict"], c["k_at_0.60"], c["k_at_0.80"], c["k_A1"], ", ".join(c["out_of_distribution"]) or "none",
                ", ".join(c["ood_and_error_relevant"]) or "none"))
    L.append("")
    L.append("## Per-criterion detail: pool vs pooled FM (deployed set)")
    L.append("")
    pf = R["conditions"]["POOLED_FM (deployed set)"]
    L.append("| ID | Criterion | Pool median [interval used] | FM median [IQR] | coverage | KS D (null95) | energy (null95) | ID | strict | stability (10k) | error rho on pool [CI] |")
    L.append("|---|---|---|---|---|---|---|---|---|---|---|")
    for cid in CRIT + A1_CRIT:
        p = R["pool_descriptive"][cid]
        c = pf["criteria"][cid]
        er = R["error_relevance_on_pool"].get(cid, {})
        st = pf.get("bootstrap_10000", {}).get("stability", {}).get(cid)
        if not c.get("available"):
            L.append("| %s | %s | %s | unavailable: %s |||||||" % (cid, p["name"], f3(p["median"]), c["why"]))
            continue
        L.append("| %s | %s | %s [%s, %s]%s | %s [%s, %s] | %s | %s (%s) | %s (%s) | %s | %s | %s | %s %s |" % (
            cid, p["name"], f3(p["median"]), f3(p["interval_used"][0]), f3(p["interval_used"][1]), " (min-max)" if p["degenerate"] else "",
            f3(c["fm_median"]), f3(c["fm_q25"]), f3(c["fm_q75"]), f3(c["coverage"]), f3(c["ks_D"]), f3(c["ks_null95"]),
            f3(c["energy"]), f3(c["energy_null95"]), f3(c["ID"]), f3(c["ID_strict"]), f3(st, 2),
            f3(er.get("rho")), ("[%s, %s]%s" % (f3(er["ci95"][0]), f3(er["ci95"][1]), " *error-relevant*" if er.get("error_relevant") else "")) if er.get("ci95") else er.get("note", "")))
    L.append("")
    L.append("## Per-condition criterion verdicts (Y = in-distribution, n = out, - = unavailable)")
    L.append("")
    L.append("| Condition | " + " | ".join(CRIT) + " |")
    L.append("|---|" + "---|" * len(CRIT))
    for sec in ("conditions", "matched"):
        for name, c in R[sec].items():
            L.append("| %s | " % name + " | ".join(("Y" if c["criteria"][x]["ID"] else "n") if c["criteria"][x].get("available") else "-" for x in CRIT) + " |")
    L.append("")
    L.append("## Direct evidence")
    L.append("")
    a = R["direct_evidence"]["a_judge_human_agreement_on_FM"]
    L.append("**(a) Judge--human agreement on FM outputs:** n = %d human-rated FM items; unavailable. %s" % (a["n_items"], a["why"] or ""))
    L.append("")
    L.append("Reference agreement on the pool (Claude 3.7 Sonnet outputs), copied from experiment 100 receipts; mean bias = judge minus human, 0-1 scale:")
    L.append("")
    L.append("| Split | n items / tasks | Spearman | Kendall tau-b | Pearson | ICC(A,1) | MAE | judge mean | human mean | mean bias |")
    L.append("|---|---|---|---|---|---|---|---|---|---|")
    for sp, r in R["direct_evidence"]["a_reference_pool_agreement_receipts_exp100"].items():
        L.append("| %s | %d / %d | %s | %s | %s | %s | %s | %s | %s | %+.3f |" % (sp, r["n_items"], r["n_tasks"], f3(r["spearman"]), f3(r["kendall_tau_b"]), f3(r["pearson"]), f3(r["icc_A1"]), f3(r["mae"]), f3(r["mean_pred"]), f3(r["mean_target"]), r["mean_bias_judge_minus_human"]))
    L.append("")
    L.append("Recomputed here with the 1e-9 tie fix and task-cluster bootstrap (10,000 draws):")
    L.append("")
    L.append("| Split | n | Spearman [CI] | Kendall [CI] | Pearson [CI] | ICC(A,1) [CI] | MAE [CI] | judge / human mean | bias [CI] |")
    L.append("|---|---|---|---|---|---|---|---|---|")
    for sp, r in R["direct_evidence"]["a_reference_pool_agreement_recomputed_tiefixed"].items():
        def ci(m):
            c = r.get(m + "_ci95")
            return "%s [%s, %s]" % (f3(r[m]), f3(c[0]), f3(c[1])) if c else f3(r[m])
        L.append("| %s | %d (%d tasks) | %s | %s | %s | %s | %s | %s / %s | %s |" % (sp, r["n_items"], r["n_tasks"], ci("spearman"), ci("kendall_tau_b"), ci("pearson"), ci("icc_A1"), ci("mae"), f3(r["mean_judge"]), f3(r["mean_human"]), ci("mean_bias_judge_minus_human")))
    L.append("")
    L.append("**(b, c) Judge repeat SD, member disagreement and score distribution (0-1 scale), FM vs pool; differences are FM minus pool with task-cluster 95% CI (10,000 draws):**")
    L.append("")
    L.append("| Condition | n | mean repeat SD (Sol/Opus) | diff vs pool [CI] | mean member disagreement | diff [CI] | H2 mean | H2 median | frac = 1.0 | diff mean vs pool [CI] | KS D (null95) | frac in pool [P5,P95] |")
    L.append("|---|---|---|---|---|---|---|---|---|---|---|---|")
    for name, s in R["direct_evidence"]["b_c_judge_side"].items():
        if s.get("available") is False:
            L.append("| %s | unavailable: %s ||||||||||" % (name, s["why"]))
            continue
        def d(k):
            v = s.get(k)
            return "[%+.3f, %+.3f]" % tuple(v) if v else ""
        L.append("| %s | %d | %s (%s/%s) | %s | %s | %s | %s | %s | %s | %s | %s | %s |" % (
            name, s["n"], f3(s["mean_repeat_sd_both_0_1"]), f3(s["mean_repeat_sd_sol_0_1"]), f3(s["mean_repeat_sd_opus_0_1"]),
            d("diff_repeat_sd_vs_pool_ci95"), f3(s["mean_member_disagreement_0_1"]), d("diff_member_disagreement_vs_pool_ci95"),
            f3(s["h2_mean"]), f3(s["h2_median"]), f3(s["h2_frac_eq_1"]), d("diff_h2_mean_vs_pool_ci95"),
            ("%s (%s)" % (f3(s["h2_ks_D_vs_pool"]), f3(s["h2_ks_null95"]))) if "h2_ks_D_vs_pool" in s else "", f3(s.get("h2_frac_in_pool_P5_P95"))))
    L.append("")
    L.append("## Disclosures")
    L.append("")
    L.append("- Error relevance (section 6) read human ratings of all 75 pool items including the 10 test tasks; it selects and changes no judge. The H2 test numbers above are the one-shot Phase-5 read for H2's selection (`results/TEST_RECEIPT.json`); other judge versions have also read the test split (at least: the 3 saved judges re-scored in exp 100 Phase 0, exp 75's finalist, and exp 104's cross-validated recipe), so the exact count is unresolved; quote ~0.15 Spearman selection inflation and exp 104's cross-validated 0.60 beside 0.83.")
    L.append("- Amendment A1 (main-function rule) and the let/have parser fix were found in the pre-registered step-6 extractor check, before any pool/FM criterion value was computed; k with A1 is reported beside, never instead of, the pre-registered k.")
    L.append("- Bootstrap draws: CRITERIA.md fixes 2,000; the orchestrator requested 10,000; both are reported.")
    L.append("- exp 107 judge values are SEALED (rating round open; Brando is rater A1); J1/J2 are unavailable there, so its k is out of 13. Its file-side values come from the public blinded packets only.")
    L.append("- ID on these criteria is not judge validation on FM outputs; only human ratings of FM outputs can validate the judge there.")
    L.append("- Data checks: %s" % json.dumps(R["data_checks"]["missing_by_condition"]))
    L.append("")
    L.append("## Verification addendum (10-09-2026): informative criteria and missing outputs")
    L.append("")
    L.append("Criteria whose pool interval already spans the whole feasible range cannot be out of distribution for any FM set; they are reported as vacuous and excluded from k_informative. Missing outputs (no file) counted as outside the pool interval give k_missing_as_outside; matched-task rows now count exp 103 pool tasks with no output.")
    L.append("")
    L.append("| Condition | k/N | vacuous | k_informative/N_informative | missing | k missing-as-outside |")
    L.append("|---|---|---|---|---|---|")
    for sec in ("conditions", "matched"):
        for name, c in R[sec].items():
            L.append("| %s | %d/%d | %s | %d/%d | %d | %s |" % (name, c["k"], c["N"], ", ".join(c["vacuous_criteria"]) or "none",
                     c["k_informative"], c["N_informative"], c["n_missing_or_no_output"], c.get("k_missing_as_outside", "n/a")))
    with open(OUT + "/RESULTS.md", "w") as fh:
        fh.write("\n".join(L) + "\n")


if __name__ == "__main__":
    main()
