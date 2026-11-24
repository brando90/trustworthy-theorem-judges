#!/usr/bin/env python3
"""Experiment 27: edit-distance baseline feature = 1 - normalised Levenshtein distance between the agent Lean file and the gold Lean file (whitespace tokens, comments stripped).

Dated 11-24-2026. CPU only, no model calls. Runs on skampere1 (needs the packet and exp 100 input files and rapidfuzz).
Run: ~/at3477/venv/bin/python edit_distance_feature.py --data DATA_DIR --out edit_distance_11-24-2026.csv
"""
import argparse, csv, json, os, re
from pathlib import Path
from rapidfuzz.distance import Levenshtein

X = "/lfs/skampere1/0/brando9/vb100/experiments/100_karpathy_recipe_tc_judge_search_human_train_val_test"
PKG = Path(os.path.expanduser("~/at3449/pkg"))


def toks(t):
    t = re.sub(r"/-.*?-/", " ", t, flags=re.S)
    t = re.sub(r"--[^\n]*", " ", t)
    return t.split()


def sim(a, b):
    ta, tb = toks(a), toks(b)
    d = Levenshtein.distance(ta, tb)
    return 1 - d / max(1, max(len(ta), len(tb)))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--data", required=True); ap.add_argument("--out", required=True)
    a = ap.parse_args()
    old = {}
    for l in open(f"{X}/inputs/items.jsonl"):
        r = json.loads(l); old[r["item"]] = r
    imap = json.load(open(PKG / "itemmap.json"))
    rows = []
    for st in ("old", "new"):
        for r in csv.DictReader(open(f"{a.data}/human_ratings_{st}_11-24-2026.csv")):
            if st == "old":
                o = old[r["item"]]
                cand = Path(X, o["candidate_path"]).read_text(errors="replace"); ref = Path(X, o["ref_ann_path"]).read_text(errors="replace")
            else:
                t, f = imap[r["item"]]["task"], imap[r["item"]]["file"]
                cand = (PKG / "packet" / f).read_text(errors="replace"); ref = (PKG / "packet" / t / "gold_lean/reference.lean").read_text(errors="replace")
            rows.append((r["item"], st, round(sim(cand, ref), 6)))
    with open(a.out, "w", newline="") as f:
        w = csv.writer(f); w.writerow(["item", "set", "edit_similarity"]); w.writerows(rows)
    print(len(rows), "rows")


if __name__ == "__main__":
    main()
