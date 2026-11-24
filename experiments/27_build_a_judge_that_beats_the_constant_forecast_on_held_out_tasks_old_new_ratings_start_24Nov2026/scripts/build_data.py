#!/usr/bin/env python3
"""Experiment 27: freeze the human ratings and cached judge scores into dated, anonymised copies and write the task-level splits.

Dated 11-24-2026. CPU only, no model calls. Rater names and rater ids are dropped; ratings are sorted within an artifact.
Inputs (private working copies, read only): --old-dataset (exp 100 rows, split, ratings, cached H0/H1/H2 judge scores),
--exp21-scores (exp 21 judge_scores.csv), --sheets (33 returned rating Sheets as TSV), --astra-new / --opus-new (fresh exp 25 judge calls).
Run: python3 build_data.py --old-dataset P --exp21-scores P --sheets DIR --astra-new P --opus-new P --out ../data_11-24-2026 --freeze "Tue 11-24-2026 12:58 PST"
"""
import argparse, collections, csv, glob, json, re
from pathlib import Path
import numpy as np

SEED = 20261124
SCORE_RE = re.compile(r'"final_score_0_5"\s*:\s*(\d)')


def read_new(sheets):
    task, ratings = {}, collections.defaultdict(list)
    for f in sorted(glob.glob(f"{sheets}/*.tsv")):
        rows = list(csv.reader(open(f), delimiter="\t"))
        i = [k for k, x in enumerate(rows[0]) if x.startswith("final_score")][0]
        for r in rows[1:]:
            if len(r) < 5:
                continue
            task[r[2]] = r[3]
            v = r[i].strip() if len(r) > i else ""
            if v == "":
                continue
            x = float(v)
            assert x == int(x) and 0 <= x <= 5
            ratings[r[2]].append(int(x))
    return task, ratings


def read_judge(fn):
    got = collections.defaultdict(dict)
    for l in open(fn):
        r = json.loads(l)
        if r["status"] != "ok":
            continue
        m = set(SCORE_RE.findall(r["raw_response"]))
        if len(m) != 1:
            continue
        it, rep = r["id"].split("#r")
        got[it][int(rep)] = int(m.pop())
    return got


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for k in ("old-dataset", "exp21-scores", "sheets", "astra-new", "opus-new", "out", "freeze"):
        ap.add_argument("--" + k, required=True)
    a = ap.parse_args()
    out = Path(a.out); out.mkdir(exist_ok=True)
    d = json.load(open(a.old_dataset))
    by = collections.defaultdict(dict)
    for r in csv.DictReader(open(a.exp21_scores)):
        if r["status"] == "COMPLETE":
            by[(r["judge"], r["item"])][int(r["repeat"])] = int(r["score_0to5"])
    art = []  # one dict per artifact
    for r, i in zip(d["rows"], range(len(d["rows"]))):
        j = {"H2_sol": d["outputs"]["H2_sol"][i], "H2_opus": d["outputs"]["H2_opus"][i],
             "H2_astra": [by[("H2_astra", r["item"])][k] for k in (1, 2, 3)],
             "H0_sol": d["outputs"]["H0_sol"][i], "H0_opus": d["outputs"]["H0_opus"][i], "H1_sol": d["outputs"]["H1_sol"][i]}
        art.append({"item": r["item"], "task": r["task"], "set": "old", "split": r["split"], "ratings": sorted(r["ratings"]), "judges": j})
    task, rat = read_new(a.sheets)
    ga, go = read_judge(a.astra_new), read_judge(a.opus_new)
    new_tasks = sorted(set(task.values()))
    rng = np.random.default_rng(SEED)
    perm = [new_tasks[i] for i in rng.permutation(len(new_tasks))]
    split_of = {t: "train" for t in perm[:10]}
    split_of.update({t: "val" for t in perm[10:15]}); split_of.update({t: "test" for t in perm[15:]})
    for it in sorted(task):
        j = {"H2_astra": [ga[it][k] for k in (1, 2, 3)], "H2_opus": [go[it][k] for k in (1, 2, 3)]}
        art.append({"item": it, "task": task[it], "set": "new", "split": split_of[task[it]], "ratings": sorted(rat.get(it, [])), "judges": j})
    # ratings
    for st in ("old", "new"):
        with open(out / f"human_ratings_{st}_11-24-2026.csv", "w", newline="") as f:
            w = csv.writer(f); w.writerow(["item", "task", "set", "split", "n_ratings", "ratings_sorted_0to5_rater_identity_removed", "freeze"])
            for x in art:
                if x["set"] == st:
                    w.writerow([x["item"], x["task"], st, x["split"], len(x["ratings"]), " ".join(map(str, x["ratings"])), a.freeze if st == "new" else "exp 100 / exp 21 ratings, frozen earlier"])
    with open(out / "judge_scores_h2_11-24-2026.csv", "w", newline="") as f:
        w = csv.writer(f); w.writerow(["item", "task", "set", "judge", "repeat", "score_0to5"])
        for x in art:
            for jn, v in x["judges"].items():
                for k, s in enumerate(v, 1):
                    w.writerow([x["item"], x["task"], x["set"], jn, k, s])
    tasks = collections.OrderedDict()
    for x in art:
        tasks.setdefault((x["task"], x["set"]), x["split"])
    with open(out / "task_splits_11-24-2026.csv", "w", newline="") as f:
        w = csv.writer(f); w.writerow(["task", "set", "split", "how_assigned"])
        for (t, s), sp in sorted(tasks.items(), key=lambda kv: (kv[0][1], kv[1], kv[0][0])):
            w.writerow([t, s, sp, "exp 100 canonical split (exp 22)" if s == "old" else f"seeded permutation of the 25 sorted new task names, numpy default_rng({SEED}): first 10 train, next 5 val, last 10 test"])
    summ = collections.Counter()
    for x in art:
        summ[(x["set"], x["split"], "artifacts")] += 1; summ[(x["set"], x["split"], "ratings")] += len(x["ratings"])
    for (s, sp, k), v in sorted(summ.items()):
        print(s, sp, k, v)
    print("tasks", {s: collections.Counter(sp for (t, ss), sp in tasks.items() if ss == s) for s in ("old", "new")})
    print("new artifacts with <2 ratings:", sum(1 for x in art if x["set"] == "new" and len(x["ratings"]) < 2))


if __name__ == "__main__":
    main()
