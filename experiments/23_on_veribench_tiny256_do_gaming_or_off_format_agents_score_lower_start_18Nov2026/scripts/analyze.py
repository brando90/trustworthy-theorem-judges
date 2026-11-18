"""Paired comparisons faithful - condition per task; writes results/summary.csv and results/summary.md."""
import csv, random, math, statistics as st
from common import HERE
gate = {(r["task"], r["condition"]): r for r in csv.DictReader(open(HERE / "results/gate.csv"))}
judge = {(r["task"], r["condition"]): r for r in csv.DictReader(open(HERE / "results/judge.csv"))}
def scores(k):
    g, j = gate[k], judge[k]
    s = float(j["judge_score"]) if j["judge_score"] != "" else 0.0  # unparseable judge output scored 0 and counted below
    return {"judge_only": s, "gated": s * int(g["passes_gate"]), "gated_format": s * int(g["passes_gate_and_format"])}
def sign_p(d):
    n = sum(x != 0 for x in d); k = sum(x > 0 for x in d)
    if n == 0: return 1.0
    p = sum(math.comb(n, i) for i in range(n + 1) if min(i, n - i) <= min(k, n - k)) / 2 ** n
    return min(1.0, p)
tasks = sorted({t for t, _ in gate}); conds = sorted({c for _, c in gate} - {"faithful_gold_copy"})
rows = []
for c in ["faithful_gold_copy"] + conds:
    for m in ["judge_only", "gated", "gated_format"]:
        ts = [t for t in tasks if (t, c) in gate and (t, c) in judge and (t, "faithful_gold_copy") in judge]
        vals = [scores((t, c))[m] for t in ts]
        d = [scores((t, "faithful_gold_copy"))[m] - scores((t, c))[m] for t in ts]
        rng = random.Random(0); boots = sorted(st.mean(rng.choices(d, k=len(d))) for _ in range(10000))
        lo, hi = boots[249], boots[9749]
        rows.append(dict(condition=c, score=m, n_tasks=len(ts), mean_score=round(st.mean(vals), 2),
                         mean_drop_vs_faithful=round(st.mean(d), 2), ci95_low=round(lo, 2), ci95_high=round(hi, 2),
                         sign_test_p=round(sign_p(d), 4), scores_lower=int(c != "faithful_gold_copy" and lo > 0 and st.mean(d) >= 1),
                         gate_pass_rate=f"{sum(int(gate[(t,c)]['passes_gate']) for t in ts)}/{len(ts)}",
                         compile_rate=f"{sum(int(gate[(t,c)]['compiles']) for t in ts)}/{len(ts)}",
                         judge_unparsed=sum(judge[(t,c)]["judge_score"] == "" for t in ts)))
with open(HERE / "results/summary.csv", "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)
hdr = list(rows[0]); md = ["| " + " | ".join(hdr) + " |", "|" + "---|" * len(hdr)] + ["| " + " | ".join(str(r[h]) for h in hdr) + " |" for r in rows]
(HERE / "results/summary.md").write_text("\n".join(md) + "\n"); print("\n".join(md))
