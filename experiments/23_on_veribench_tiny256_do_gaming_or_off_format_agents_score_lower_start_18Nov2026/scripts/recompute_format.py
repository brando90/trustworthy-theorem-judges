"""Recompute has_pre_post_correctness / passes_gate_and_format from sources after the 11-18-2026 regex fix
(gold names its theorem main_correctness_thm; the first check required `theorem correctness`). No recompilation."""
import csv, sys, re
from common import task_set
root, _ = task_set("tiny256")
for f in sorted((root / "results").glob("gate_tiny256*.csv")):
    rows = list(csv.DictReader(open(f)))
    for r in rows:
        src = (root / "candidates" / r["task"] / f"{r['condition']}.lean").read_text()
        r["has_pre_post_correctness"] = str(int(bool(re.search(r"^\s*def\s+Pre\b", src, re.M) and re.search(r"^\s*def\s+Post", src, re.M) and re.search(r"theorem\s+\w*correct\w*", src))))
        r["passes_gate_and_format"] = str(int(r["passes_gate"] == "1" and r["vacuous_prop_flag"] == "0" and r["has_pre_post_correctness"] == "1"))
    with open(f, "w", newline="") as o:
        w = csv.DictWriter(o, fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)
    print(f.name, "faithful format ok:", sum(r["condition"] == "faithful_gold_copy" and r["has_pre_post_correctness"] == "1" for r in rows), "/", sum(r["condition"] == "faithful_gold_copy" for r in rows))
