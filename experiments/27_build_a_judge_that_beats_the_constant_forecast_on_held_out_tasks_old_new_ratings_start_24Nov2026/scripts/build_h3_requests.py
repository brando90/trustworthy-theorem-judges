#!/usr/bin/env python3
"""Experiment 27: render the H3 judge prompt (pooled train demonstrations, train base rate, score_distribution output) for all 175 artifacts.

Dated 11-24-2026. NO model calls. Runs on skampere1 (needs the exp 100 prompt code and the packet files). Writes requests_h3_trainval.jsonl
(train and validation artifacts, run first), requests_h3_test.jsonl (test artifacts, run only after the freeze commit) and a demo manifest that
the leakage check reads. Demonstrations and the base rate come only from TRAIN tasks; an item never sees a demonstration from its own task.
Run: cd ~/at3477 && python3 build_h3_requests.py --data data_11-24-2026 --out h3
"""
import argparse, csv, hashlib, json, os, sys
from collections import Counter
from pathlib import Path

X = "/lfs/skampere1/0/brando9/vb100/experiments/100_karpathy_recipe_tc_judge_search_human_train_val_test"
sys.path.insert(0, X + "/scripts"); os.chdir(X)
import prompts, common  # noqa: E402
from build_inputs import statements  # noqa: E402

PKG = Path(os.path.expanduser("~/at3449/pkg"))
QS = (0.15, 0.85)
OUT_FORMAT = ('Answer with ONLY one JSON object (no markdown fences) with exactly these keys:\n'
              '{"A": "Y" or "N", "B": "Y" or "N", "C": "Y" or "N", "D": "handful" or "dominates" or "N/A", "base_score": integer 0-5, '
              '"final_score_0_5": integer 0-5, "score_distribution": {"0": p0, "1": p1, "2": p2, "3": p3, "4": p4, "5": p5}, '
              '"confidence": "Low" or "Med" or "High", "rationale": "2-4 sentences naming at least one covered and one uncovered gold theorem if any, and spam examples if C=Y"}\n'
              'score_distribution gives your probability that a randomly drawn expert rater scores this item 0, 1, 2, 3, 4 or 5; the six numbers are non-negative and sum to 1.')


def load(data):
    split = {r["task"]: r["split"] for r in csv.DictReader(open(f"{data}/task_splits_11-24-2026.csv"))}
    old_items = {r["item"]: r for r in common.load_items("all")}
    imap = json.load(open(PKG / "itemmap.json"))
    arts = []
    for st in ("old", "new"):
        for r in csv.DictReader(open(f"{data}/human_ratings_{st}_11-24-2026.csv")):
            rat = [int(x) for x in r["ratings_sorted_0to5_rater_identity_removed"].split()]
            a = {"item": r["item"], "task": r["task"], "set": st, "split": r["split"], "ratings": rat, "mean": sum(rat) / len(rat)}
            assert split[r["task"]] == r["split"]
            if st == "old":
                o = old_items[r["item"]]
                a.update(ref=o["ref_ann_path"], py=o["py_ann_path"], gold_name=o["gold_file_name"], cand_name=o["candidate_file"],
                         cand_text=common.read_text(o["candidate_path"]), placeholder=bool(o.get("ref_placeholder_at_annotation")))
            else:
                t, f = imap[r["item"]]["task"], imap[r["item"]]["file"]
                a.update(ref=str(PKG / "packet" / t / "gold_lean/reference.lean"), py=str(PKG / "packet" / t / "python_source/source.py"),
                         gold_name="reference.lean", cand_name=Path(f).name, cand_text=(PKG / "packet" / f).read_text(), placeholder=False)
            arts.append(a)
    return arts


def pick_demos(arts, item):
    chosen, used = [], {item["task"]}
    for st in ("old", "new"):
        pool = [a for a in arts if a["split"] == "train" and a["set"] == st and a["task"] != item["task"] and not a["placeholder"]]
        means = sorted(a["mean"] for a in pool)
        for q in QS:
            goal = means[min(len(means) - 1, int(round(q * (len(means) - 1))))]
            best = min((a for a in pool if a["task"] not in used), key=lambda a: (abs(a["mean"] - goal), a["item"]))
            chosen.append(best); used.add(best["task"])
    return chosen


def demo_block(demos, base_rate_line, max_lines=90):
    parts = ["<rated_examples>\nThe expert raters scored these items from other tasks. Use them to match the raters' scale; do not copy scores across tasks.\n" + base_rate_line + "\n"]
    for i, d in enumerate(demos, 1):
        cand = d["cand_text"].splitlines()[:max_lines]
        scores = ", ".join(f"P{k}={s}" for k, s in enumerate(d["ratings"], 1))
        parts.append(prompts.DEMO_TEMPLATE.format(i=i, task=d["task"], gold="\n".join(statements(common.read_text(d["ref"]))),
                                                  lines=max_lines, cand="\n".join(cand), scores=scores, mean=d["mean"]))
    return "\n".join(parts) + "</rated_examples>"


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--data", required=True); ap.add_argument("--out", required=True)
    a = ap.parse_args()
    arts = load(a.data)
    tr = [r for x in arts if x["split"] == "train" for r in x["ratings"]]
    c = Counter(tr); n = len(tr)
    base = ("Base rate of expert scores over all rated training items (both batches pooled, %d ratings): 5 = %d%%, 4 = %d%%, 3 = %d%%, 2 or lower = %d%%. "
            "Expert raters follow the tie-break rule, so a score of 5 is common for files that cover all gold guarantees and rare otherwise."
            % (n, round(100 * c[5] / n), round(100 * c[4] / n), round(100 * c[3] / n), round(100 * sum(v for k, v in c.items() if k <= 2) / n)))
    rows = {"trainval": [], "test": []}; manifest = {}
    for x in arts:
        it = {"item": x["item"], "task": x["task"], "ref_ann_path": x["ref"], "py_ann_path": x["py"], "gold_file_name": x["gold_name"]}
        if x["set"] == "old":
            it["ref_snap_path"] = x["ref"]
        system, user = prompts.render("H2_human_mirror_conventions_demos", it, x["cand_text"], x["cand_name"])
        i, j = system.index("<rated_examples>"), system.index("</rated_examples>") + len("</rated_examples>")
        demos = pick_demos(arts, x)
        k = system.index("Answer with ONLY one JSON object")
        system = system[:i] + demo_block(demos, base) + "\n\n" + OUT_FORMAT
        manifest[x["item"]] = {"task": x["task"], "split": x["split"], "demo_items": [d["item"] for d in demos], "demo_tasks": [d["task"] for d in demos]}
        rows["test" if x["split"] == "test" else "trainval"].append({"id": x["item"] + "#r1", "split": x["split"], "system": system, "user": user})
    os.makedirs(a.out, exist_ok=True)
    for k, v in rows.items():
        data = "".join(json.dumps(r, ensure_ascii=False) + "\n" for r in v).encode()
        Path(f"{a.out}/requests_h3_{k}.jsonl").write_bytes(data)
        print(k, len(v), "requests, sha256", hashlib.sha256(data).hexdigest(), "max chars", max(len(r["system"]) + len(r["user"]) for r in v))
    json.dump({"base_rate_line": base, "items": manifest}, open(f"{a.out}/h3_demo_manifest.json", "w"), indent=1)
    train_tasks = {x["task"] for x in arts if x["split"] == "train"}
    bad = [i for i, m in manifest.items() if any(t not in train_tasks or t == m["task"] for t in m["demo_tasks"])]
    print("leakage check: demos outside train tasks or from own task:", len(bad)); print(base)


if __name__ == "__main__":
    main()
