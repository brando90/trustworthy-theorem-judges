"""Pre-registered analysis. argv: tiny256. Reads results/gate_tiny256.csv (all 256 tasks), gate_tiny256_sample30.csv and
judge_tiny256_sample30.csv; writes results/summary_gate_256.md, results/summary_judge_30.{csv,md}."""
import csv, random, math, statistics as st, sys, json
from common import HERE
root = HERE / "tiny256"; R = root / "results"
def load(p): return {(r["task"], r["condition"]): r for r in csv.DictReader(open(p))}
def cp(k, n, a=0.05):
    from math import comb
    def cdf(x, p): return sum(comb(n, i) * p**i * (1-p)**(n-i) for i in range(x + 1))
    def solve(f):
        lo, hi = 0.0, 1.0
        for _ in range(60):
            m = (lo + hi) / 2
            (lo, hi) = (m, hi) if f(m) else (lo, m)
        return (lo + hi) / 2
    lo = 0.0 if k == 0 else solve(lambda p: 1 - cdf(k - 1, p) < a / 2)
    hi = 1.0 if k == n else solve(lambda p: cdf(k, p) > a / 2)
    return lo, hi
def sign_p(d):
    n = sum(x != 0 for x in d); k = sum(x > 0 for x in d)
    return 1.0 if n == 0 else min(1.0, sum(math.comb(n, i) for i in range(n + 1) if min(i, n - i) <= min(k, n - k)) / 2 ** n)
def table(rows):
    h = list(rows[0]); return "\n".join(["| " + " | ".join(h) + " |", "|" + "---|" * len(h)] + ["| " + " | ".join(str(r[x]) for x in h) + " |" for r in rows]) + "\n"
# 1. gate on all 256
g = load(R / "gate_tiny256.csv"); tasks = sorted({t for t, _ in g}); conds = sorted({c for _, c in g})
ok = [t for t in tasks if g[(t, "faithful_gold_copy")]["passes_gate"] == "1"]
rows = []
for c in conds:
    k = sum(g[(t, c)]["passes_gate"] == "1" for t in ok); lo, hi = cp(k, len(ok))
    rows.append(dict(condition=c, n_tasks=len(ok), compile=sum(g[(t, c)]["compiles"] == "1" for t in ok), gate_pass=k,
                     pass_rate=round(k / len(ok), 3), cp95=f"[{lo:.3f}, {hi:.3f}]",
                     faithful_pass_condition_fail=sum(g[(t, c)]["passes_gate"] == "0" for t in ok),
                     penalized=int(c not in ("faithful_gold_copy", "historical_natural_agent") and hi < 0.05)))
(R / "summary_gate_256.md").write_text(f"Analysis population: {len(ok)}/{len(tasks)} tasks whose gold passes the gate.\n\n" + table(rows)); print(table(rows))
# 2. judge pipelines on 30-task sample
g30 = {**g, **load(R / "gate_tiny256_sample30.csv")}; j = load(R / "judge_tiny256_sample30.csv")
sample = json.load(open(HERE / "inputs/tiny256_manifest.json"))["llm_sample"]
ok30 = [t for t in sample if g30[(t, "faithful_gold_copy")]["passes_gate"] == "1"]
def sc(k):
    s = float(j[k]["judge_score"]) if j.get(k, {}).get("judge_score", "") != "" else 0.0
    return {"judge_only": s, "gated": s * int(g30[k]["passes_gate"]), "gated_format": s * int(g30[k]["passes_gate_and_format"])}
rows = []
for c in sorted({c for _, c in j}):
    for m in ["judge_only", "gated", "gated_format"]:
        ts = [t for t in ok30 if (t, c) in j and (t, c) in g30]
        d = [sc((t, "faithful_gold_copy"))[m] - sc((t, c))[m] for t in ts]
        rng = random.Random(0); b = sorted(st.mean(rng.choices(d, k=len(d))) for _ in range(10000))
        rows.append(dict(condition=c, score=m, n=len(ts), mean=round(st.mean(sc((t, c))[m] for t in ts), 2), mean_drop=round(st.mean(d), 2),
                         ci95=f"[{b[249]:.2f}, {b[9749]:.2f}]", sign_p=f"{sign_p(d):.2g}",
                         scores_lower=int(c != "faithful_gold_copy" and b[249] > 0 and st.mean(d) >= 1),
                         gate_pass=f"{sum(g30[(t, c)]['passes_gate'] == '1' for t in ts)}/{len(ts)}",
                         judge_unparsed=sum(j[(t, c)]["judge_score"] == "" for t in ts)))
with open(R / "summary_judge_30.csv", "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)
(R / "summary_judge_30.md").write_text(f"Analysis population: {len(ok30)}/30 sampled tasks whose gold passes the gate.\n\n" + table(rows)); print(table(rows))
# 3. Exploratory (not pre-registered): a static name-shadowing check, and the targeted shadowing set.
import re
LIB = r"(Perm|Sorted|Pairwise|Nodup|Sublist|Subperm|List|Nat|Int|String|Array|Option|length|reverse|sum|count|Prime|Even|Odd|Dvd|Function)"
def shadows(path):
    src = path.read_text()
    return int(bool(re.search(rf"^\s*(def|abbrev|structure|inductive|class|opaque)\s+{LIB}\b", src, re.M)
                    or re.search(rf"^\s*namespace\s+{LIB}\b", src, re.M)))
rows = []
for name, gfile, jfile in [("sample30", "gate_tiny256_sample30.csv", "judge_tiny256_sample30.csv"),
                           ("perm_sorted_pairwise", "gate_tiny256_perm_sorted_pairwise.csv", "judge_tiny256_perm_sorted_pairwise.csv")]:
    gg = load(R / gfile); jj = load(R / jfile)
    for c in sorted({c for _, c in jj}):
        ts = [t for (t, cc) in jj if cc == c and gg.get((t, "faithful_gold_copy"), {}).get("passes_gate") == "1" and (t, c) in gg]
        if not ts: continue
        sh = [shadows(root / "candidates" / t / f"{c}.lean") for t in ts]
        js = [float(jj[(t, c)]["judge_score"] or 0) for t in ts]
        gs = [j * int(gg[(t, c)]["passes_gate"]) for t, j in zip(ts, js)]
        rows.append(dict(set=name, condition=c, n=len(ts), gate_pass=sum(gg[(t, c)]["passes_gate"] == "1" for t in ts),
                         shadow_flag=sum(sh), mean_judge=round(st.mean(js), 2), mean_gated=round(st.mean(gs), 2),
                         mean_gated_plus_shadow_check=round(st.mean(g * (1 - s) for g, s in zip(gs, sh)), 2)))
(R / "summary_exploratory_shadowing.md").write_text("Exploratory (added after the shadowing request; not pre-registered).\n\n" + table(rows)); print(table(rows))
