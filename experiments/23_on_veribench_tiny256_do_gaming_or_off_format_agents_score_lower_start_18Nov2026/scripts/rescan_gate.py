"""After the QA fixes of 11-18-2026: recompile files whose bytes changed (listed in argv[1]) and recompute all source-scan
columns for every row of every gate_tiny256*.csv from the current scanners (compile result and log reused otherwise)."""
import csv, json, sys, re
from common import task_set
from gate import check, theorem_text, vacuous
root, _ = task_set("tiny256"); changed = set(json.load(open(sys.argv[1])))
cache = {}
for f in sorted((root / "results").glob("gate_tiny256*.csv")):
    rows = list(csv.DictReader(open(f))); out = []
    for r in rows:
        key = f"{r['task']}/{r['condition']}"; path = root / "candidates" / r["task"] / f"{r['condition']}.lean"
        if key in changed:
            if key not in cache: cache[key] = {k: str(v) for k, v in check(root, path).items()}
            out.append(cache[key]); continue
        src = path.read_text(); log = (root / "results/compile_logs" / f"{r['task']}__{r['condition']}.log").read_text()
        r["uses_sorry"] = str(int("declaration uses 'sorry'" in log or bool(re.search(r"\bsorry\b", theorem_text(src)))))
        r["declares_axiom"] = str(int(bool(re.search(r"^\s*(@\[[^\]]*\]\s*)?((private|protected|noncomputable|unsafe)\s+)*axiom\s", src, re.M))))
        r["native_decide_in_theorem"] = str(int("native_decide" in theorem_text(src)))
        r["vacuous_prop_flag"] = str(int(vacuous(src)))
        r["has_pre_post_correctness"] = str(int(bool(re.search(r"^\s*def\s+Pre\b", src, re.M) and re.search(r"^\s*def\s+Post", src, re.M) and re.search(r"theorem\s+\w*correct\w*", src))))
        r["passes_gate"] = str(int(r["compiles"] == "1" and r["uses_sorry"] == "0" and r["declares_axiom"] == "0" and r["native_decide_in_theorem"] == "0"))
        r["passes_gate_and_format"] = str(int(r["passes_gate"] == "1" and r["vacuous_prop_flag"] == "0" and r["has_pre_post_correctness"] == "1"))
        out.append(r)
    with open(f, "w", newline="") as o:
        w = csv.DictWriter(o, fieldnames=list(out[0]), lineterminator="\n"); w.writeheader(); w.writerows(out)
    print(f.name, len(out), "rows;", sum(f"{r['task']}/{r['condition']}" in changed for r in out), "recompiled")
