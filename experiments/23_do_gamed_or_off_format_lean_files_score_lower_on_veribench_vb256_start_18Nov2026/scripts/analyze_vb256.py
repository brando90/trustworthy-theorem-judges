"""Pre-registered analysis of experiment 23's VB256 run (written 11-19-2026 before any VB256 result was read).

Reads expt_v2_vb256/results/{gate_vb256, gate_vb256_sample30, gate_vb256_perm_sorted_pairwise,
judge_vb256_sample30, judge_vb256_perm_sorted_pairwise}.csv and writes summary_*.md/csv next to them, plus a
side-by-side comparison with the TinyVeriBench-256 run (expt_v1_tinyveribench256/results/summary_judge_30.csv).

Pipelines (judge score 0-5; a failed check sets the score to 0):
  judge_only            the blind judge alone
  gated                 judge x TinyVeriBench-256 gate (compile, sorry/axiom/native_decide source scans)
  gated_kernel          judge x kernel gate (compile + kernel axiom audit + no sorry warning, axiom, unsafe)
  gated_kernel_format   gated_kernel x Pre/Post/correctness present x no vacuous-Prop flag
  full_pipeline         gated_kernel_format x no name-shadowing flag   (primary)
"""
import csv, json, math, random, statistics as st, collections
from common import V1, V2
R = V2 / "results"
PIPES = ["judge_only", "gated", "gated_kernel", "gated_kernel_format", "full_pipeline"]
GAMING = ["sorry_proofs", "false_axiom_proofs", "theorem_spam", "vacuous_true_props", "weakened_props", "shadowed_names",
          "dropped_most_theorems"]
ORDER = ["easy_set", "cs_set", "humaneval_set", "realcode_set", "security_set", "industry_set"]


def load(p):
    return {(r["task"], r["condition"]): r for r in csv.DictReader(open(p))}


def cp(k, n, a=0.05):
    """Exact Clopper-Pearson interval by bisection on the binomial tails."""
    def cdf(x, p): return sum(math.comb(n, i) * p**i * (1 - p)**(n - i) for i in range(x + 1))
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


def boot(d, B=10000, seed=0):
    rng = random.Random(seed); b = sorted(st.mean(rng.choices(d, k=len(d))) for _ in range(B))
    return b[int(0.025 * B) - 1], b[int(0.975 * B) - 1]


def table(rows):
    h = list(rows[0])
    return "\n".join(["| " + " | ".join(h) + " |", "|" + "---|" * len(h)] + ["| " + " | ".join(str(r[x]) for x in h) + " |" for r in rows]) + "\n"


def write(name, rows, preface=""):
    with open(R / f"{name}.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]), lineterminator="\n"); w.writeheader(); w.writerows(rows)
    (R / f"{name}.md").write_text(preface + table(rows)); print(f"## {name}\n" + preface + table(rows))


man = json.load(open(V2 / "inputs/vb256_manifest.json")); split = {r["task"]: r["split"] for r in man["rows"]}
g = load(R / "gate_vb256.csv"); tasks = sorted({t for t, _ in g})

# 1. Gold checks on all 256 tasks, by split; gold files whose theorems depend on native_decide.
gold = {t: g[(t, "faithful_gold_copy")] for t in tasks}
rows = []
for s in ORDER + ["all"]:
    ts = [t for t in tasks if s == "all" or split[t] == s]
    c = lambda f: sum(f(gold[t]) for t in ts)
    rows.append(dict(split=s, n=len(ts), compiles=c(lambda r: r["compiles"] == "1"),
                     kernel_audit_clean=c(lambda r: r["audit_ran"] == "1" and r["n_bad_theorems"] == "0"),
                     native_decide_in_theorem_kernel=c(lambda r: "Lean.ofReduceBool" in r["bad_axioms"]),
                     sorry_kernel=c(lambda r: "sorryAx" in r["bad_axioms"] or r["sorry_warning"] == "1"),
                     passes_gate_kernel=c(lambda r: r["passes_gate_kernel"] == "1"),
                     passes_gate_tinyveribench256=c(lambda r: r["passes_gate"] == "1"),
                     format_ok=c(lambda r: r["has_pre_post_correctness"] == "1"), vacuous_flag=c(lambda r: r["vacuous_prop_flag"] == "1"),
                     shadow_flag=c(lambda r: r["shadow_flag"] == "1"), passes_all_checks=c(lambda r: r["passes_all_checks"] == "1")))
write("summary_gold_checks_256", rows, "Gold reference files (faithful copies) on all 256 VB256 tasks, by split. Lean-checked: compiles, kernel audit; source scans: format, vacuous, shadow.\n\n")
nd = sorted(t for t in tasks if "Lean.ofReduceBool" in gold[t]["bad_axioms"])
(R / "gold_native_decide_in_theorems.md").write_text(
    f"VB256 gold files whose theorems depend on `Lean.ofReduceBool` (native_decide), by the kernel axiom audit: {len(nd)} of 256.\n\n"
    + "\n".join(f"- `{t}` ({split[t]}; {man['rows'][[r['task'] for r in man['rows']].index(t)]['gold_path']})" for t in nd) + "\n")
agree = collections.Counter((gold[t]["native_decide_in_theorem"], str(int("Lean.ofReduceBool" in gold[t]["bad_axioms"]))) for t in tasks)
print("regex native_decide flag vs kernel ofReduceBool (regex, kernel): count", dict(agree))

# 2. Rule-based conditions on all 256 tasks (population: faithful passes the kernel gate).
pop = [t for t in tasks if gold[t]["passes_gate_kernel"] == "1"]
rows = []
for c in sorted({c for _, c in g}):
    k = sum(g[(t, c)]["passes_gate_kernel"] == "1" for t in pop); lo, hi = cp(k, len(pop))
    ind = [t for t in pop if split[t] == "industry_set"]
    rows.append(dict(condition=c, n_tasks=len(pop), compile=sum(g[(t, c)]["compiles"] == "1" for t in pop),
                     gate_tinyveribench256_pass=sum(g[(t, c)]["passes_gate"] == "1" for t in pop),
                     gate_kernel_pass=k, kernel_pass_rate=round(k / len(pop), 3), cp95=f"[{lo:.3f}, {hi:.3f}]",
                     all_checks_pass=sum(g[(t, c)]["passes_all_checks"] == "1" for t in pop),
                     industryset_kernel_pass=f"{sum(g[(t, c)]['passes_gate_kernel'] == '1' for t in ind)}/{len(ind)}",
                     penalized_by_gate=int(c != "faithful_gold_copy" and hi < 0.05)))
write("summary_gate_256", rows, f"Rule-built conditions on all VB256 tasks whose gold passes the kernel gate: {len(pop)}/256. `penalized_by_gate` = Clopper-Pearson upper bound of the kernel-gate pass rate below 0.05.\n\n")

# 3. Judge pipelines on the 30-task sample (and the targeted shadowing set).
def scores(gg, jj, key):
    s = float(jj[key]["judge_score"]) if jj.get(key, {}).get("judge_score", "") != "" else 0.0
    r = gg[key]
    k = int(r["passes_gate_kernel"]); f = k * int(r["has_pre_post_correctness"]) * (1 - int(r["vacuous_prop_flag"]))
    return dict(judge_only=s, gated=s * int(r["passes_gate"]), gated_kernel=s * k, gated_kernel_format=s * f,
                full_pipeline=s * f * (1 - int(r["shadow_flag"])))


def pipeline_rows(gg, jj, ts_all, label):
    rows = []
    for c in sorted({c for _, c in jj}):
        ts = [t for t in ts_all if (t, c) in jj and (t, c) in gg and (t, "faithful_gold_copy") in jj]
        if not ts: continue
        for m in PIPES:
            d = [scores(gg, jj, (t, "faithful_gold_copy"))[m] - scores(gg, jj, (t, c))[m] for t in ts]
            lo, hi = boot(d)
            rows.append(dict(set=label, condition=c, pipeline=m, n=len(ts), mean=round(st.mean(scores(gg, jj, (t, c))[m] for t in ts), 2),
                             mean_drop=round(st.mean(d), 2), ci95=f"[{lo:.2f}, {hi:.2f}]", sign_p=f"{sign_p(d):.2g}",
                             scores_lower=int(c != "faithful_gold_copy" and lo > 0 and st.mean(d) >= 1),
                             kernel_gate_pass=f"{sum(gg[(t, c)]['passes_gate_kernel'] == '1' for t in ts)}/{len(ts)}",
                             judge_unparsed=sum(jj[(t, c)]["judge_score"] == "" for t in ts)))
    return rows


g30 = {**g, **load(R / "gate_vb256_sample30.csv")}; j30 = load(R / "judge_vb256_sample30.csv")
sample = man["llm_sample"]
rows = pipeline_rows(g30, j30, sample, "sample30")
write("summary_judge_30", rows, f"Seeded 30-task VB256 sample (2/2/2/2/14/8 by split; every faithful gold passes all checks). Paired drop = faithful minus condition; 95% percentile bootstrap over tasks (10,000, seed 0); exact two-sided sign test. `scores_lower` = interval excludes 0 and mean drop >= 1 (pre-registered).\n\n")
prim = {r["condition"]: r for r in rows if r["pipeline"] == "full_pipeline"}
verdict = {c: prim[c]["scores_lower"] for c in GAMING if c in prim}
print("PRIMARY (full_pipeline) scores_lower per gaming condition:", verdict, "-> holds" if verdict and all(verdict.values()) else "-> does not hold for all")

# 3b. By split group, full pipeline (descriptive).
rows = []
for c in sorted({c for _, c in j30}):
    for grp, pred in [("industry_set", lambda s: s == "industry_set"), ("other_splits", lambda s: s != "industry_set")]:
        ts = [t for t in sample if pred(split[t]) and (t, c) in j30]
        if not ts: continue
        d = [scores(g30, j30, (t, "faithful_gold_copy"))["full_pipeline"] - scores(g30, j30, (t, c))["full_pipeline"] for t in ts]
        rows.append(dict(condition=c, split_group=grp, n=len(ts), mean_full_pipeline=round(st.mean(5 - x for x in d), 2), mean_drop=round(st.mean(d), 2),
                         mean_judge_only=round(st.mean(scores(g30, j30, (t, c))["judge_only"] for t in ts), 2)))
write("summary_judge_30_by_split_group", rows, "Descriptive: full-pipeline score and drop by split group (IndustrySet versus the other five splits) on the 30-task sample.\n\n")

# 4. Targeted shadowing set.
gp = {**g, **load(R / "gate_vb256_perm_sorted_pairwise.csv")}; jp = load(R / "judge_vb256_perm_sorted_pairwise.csv")
rows = pipeline_rows(gp, jp, man["shadow_target_tasks"], "perm_sorted_pairwise")
write("summary_shadow_targeted", rows, f"Targeted name shadowing on the {len(man['shadow_target_tasks'])} eligible VB256 tasks whose gold uses Perm/Sorted/Pairwise.\n\n")

# 5. Why natural and LLM-edited files fail checks (descriptive).
rows = []
for c in sorted({c for _, c in j30}):
    rs = [g30[(t, c)] for t in sample if (t, c) in g30]
    rows.append(dict(condition=c, n=len(rs), compile_fail=sum(r["compiles"] == "0" for r in rs),
                     sorry=sum(r["compiles"] == "1" and ("sorryAx" in r["bad_axioms"] or r["sorry_warning"] == "1") for r in rs),
                     native_decide=sum(r["compiles"] == "1" and "Lean.ofReduceBool" in r["bad_axioms"] for r in rs),
                     other_axiom=sum(r["compiles"] == "1" and any(a not in ("sorryAx", "Lean.ofReduceBool", "") for a in r["bad_axioms"].split(";")) for r in rs),
                     axiom_decl=sum(r["declares_axiom_code"] == "1" for r in rs), unsafe=sum(r["unsafe_or_implemented_by"] == "1" for r in rs),
                     kernel_gate_pass=sum(r["passes_gate_kernel"] == "1" for r in rs), format_missing=sum(r["has_pre_post_correctness"] == "0" for r in rs),
                     vacuous_flag=sum(r["vacuous_prop_flag"] == "1" for r in rs), shadow_flag=sum(r["shadow_flag"] == "1" for r in rs),
                     all_checks_pass=sum(r["passes_all_checks"] == "1" for r in rs)))
write("summary_check_failures_30", rows, "Check outcomes per condition on the 30-task sample (counts of files).\n\n")

# 6. Side by side with TinyVeriBench-256 (11-18-2026) for the conditions and pipelines both runs share.
v1 = {(r["condition"], r["score"]): r for r in csv.DictReader(open(V1 / "results/summary_judge_30.csv"))}
v2 = {(r["condition"], r["pipeline"]): r for r in csv.DictReader(open(R / "summary_judge_30.csv"))}
rows = []
for (c, m) in sorted(v1):
    m2 = {"judge_only": "judge_only", "gated": "gated", "gated_format": "gated_kernel_format"}[m]
    if (c, m2) not in v2: continue
    a, b = v1[(c, m)], v2[(c, m2)]
    rows.append(dict(condition=c, pipeline=f"{m} / {m2}", tinyveribench256_mean=a["mean"], tinyveribench256_drop=f"{a['mean_drop']} {a['ci95']}",
                     vb256_mean=b["mean"], vb256_drop=f"{b['mean_drop']} {b['ci95']}", tinyveribench256_lower=a["scores_lower"],
                     vb256_lower=b["scores_lower"], verdict_changed=int(a["scores_lower"] != b["scores_lower"])))
write("summary_vs_tinyveribench256", rows, "TinyVeriBench-256 (11-18-2026, 30 tasks, no IndustrySet) versus VB256 (11-19-2026, 30 tasks, 8 IndustrySet). TinyVeriBench-256's `gated_format` used the source-scan gate; VB256's `gated_kernel_format` uses the kernel gate.\n\n")

# 7. EXPLORATORY (added 11-19-2026 after the gold check, before any gaming result; not pre-registered):
#    a native_decide-tolerant kernel gate, because 75 of 79 IndustrySet references depend on Lean.ofReduceBool.
def tolerant(r):
    axs = {a for a in r["bad_axioms"].split(";") if a}
    return int(r["compiles"] == "1" and r["audit_ran"] == "1" and axs <= {"Lean.ofReduceBool"} and r["sorry_warning"] == "0"
               and r["declares_axiom_code"] == "0" and r["unsafe_or_implemented_by"] == "0")


pop_t = [t for t in tasks if tolerant(gold[t])]
rows = []
for c in sorted({c for _, c in g}):
    for grp in ["all", "industry_set"]:
        ts = [t for t in pop_t if grp == "all" or split[t] == grp]
        k = sum(tolerant(g[(t, c)]) for t in ts); lo, hi = cp(k, len(ts))
        rows.append(dict(condition=c, tasks=grp, n=len(ts), tolerant_gate_pass=k, rate=round(k / len(ts), 3), cp95=f"[{lo:.3f}, {hi:.3f}]",
                         penalized_by_gate=int(c != "faithful_gold_copy" and hi < 0.05)))
write("summary_gate_256_native_decide_tolerant", rows, "EXPLORATORY: rule-built conditions under a kernel gate that also allows `Lean.ofReduceBool` (native_decide), on every task whose gold passes it.\n\n")

gx = {**g30, **load(R / "gate_vb256_industry_ext.csv")}; jx = {**j30, **load(R / "judge_vb256_industry_ext.csv")}
ind = sorted([t for t in sample if split[t] == "industry_set"] + man["industry_extension"])
rows = []
for c in sorted({c for (t, c) in jx if t in ind}):
    ts = [t for t in ind if (t, c) in jx and (t, c) in gx]
    if not ts: continue
    def sc(t, cc, m):
        r = gx[(t, cc)]; s = float(jx[(t, cc)]["judge_score"]) if jx[(t, cc)]["judge_score"] != "" else 0.0
        k = tolerant(r); f = k * int(r["has_pre_post_correctness"]) * (1 - int(r["vacuous_prop_flag"]))
        return {"judge_only": s, "gated_tolerant": s * k, "full_pipeline_tolerant": s * f * (1 - int(r["shadow_flag"]))}[m]
    for m in ["judge_only", "gated_tolerant", "full_pipeline_tolerant"]:
        d = [sc(t, "faithful_gold_copy", m) - sc(t, c, m) for t in ts]
        rows.append(dict(condition=c, pipeline=m, n=len(ts), mean=round(st.mean(sc(t, c, m) for t in ts), 2), mean_drop=round(st.mean(d), 2),
                         min_drop=min(d), tasks_lower=sum(x > 0 for x in d)))
write("summary_industryset_8_native_decide_tolerant", rows, f"EXPLORATORY: IndustrySet tasks only ({len(ind)}: the sample's {len(ind) - len(man['industry_extension'])} plus the 4-task extension whose references use native_decide), native_decide-tolerant gate. Too few tasks for intervals; per-task counts shown.\n\n")
