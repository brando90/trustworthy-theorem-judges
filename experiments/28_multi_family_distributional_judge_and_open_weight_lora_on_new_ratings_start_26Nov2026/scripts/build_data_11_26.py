#!/usr/bin/env python3
"""Experiment 28: freeze anonymised human ratings (195 old + 250 live new), task splits, and cached H2/H3 features.

Dated 11-26-2026. CPU only, no model calls. Rater names and rater IDs are removed;
ratings are sorted within each artifact.
"""
from __future__ import annotations

import collections
import csv
import glob
import json
from pathlib import Path
import numpy as np

SEED_CV5 = 20261126
ROOT = Path(__file__).resolve().parents[3]
EXP27_DATA = ROOT / "experiments/27_build_a_judge_that_beats_the_constant_forecast_on_held_out_tasks_old_new_ratings_start_24Nov2026/data_11-24-2026"
EXP09_RATINGS = ROOT / "experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/ratings"
OUT_DIR = Path(__file__).resolve().parents[1] / "data_11-26-2026"
CACHE_DIR = Path("/tmp/exp28_cache")


def parse_h3_json(raw: str) -> dict:
    idx = raw.find("{")
    obj, _ = json.JSONDecoder().raw_decode(raw[idx:])
    s = int(obj["final_score_0_5"])
    d = obj["score_distribution"]
    probs = [float(d[str(k)]) for k in range(6)]
    tot = sum(probs)
    assert abs(tot - 1.0) <= 0.05 and all(p >= 0 for p in probs) and 0 <= s <= 5
    probs = [p / tot for p in probs]
    return {
        "h3_score": s,
        "probs": probs,
        "A": str(obj.get("A", "")).strip(),
        "B": str(obj.get("B", "")).strip(),
        "C": str(obj.get("C", "")).strip(),
        "D": str(obj.get("D", "")).strip(),
        "base_score": int(obj["base_score"]) if obj.get("base_score") is not None else "",
        "confidence": str(obj.get("confidence", "")).strip(),
    }


def main() -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)

    # 1. Old ratings (identical 75 artifacts / 195 expert ratings from Exp 27)
    old_rows = list(csv.DictReader((EXP27_DATA / "human_ratings_old_11-24-2026.csv").open()))
    assert len(old_rows) == 75

    # 2. Live Exp 09 ratings (all 33 manifest sheets, excluding coordinator A1 who has 0 scores)
    itemmap = json.loads((CACHE_DIR / "itemmap.json").read_text())
    assert len(itemmap) == 100
    new_ratings_by_item: dict[str, list[int]] = collections.defaultdict(list)
    active_raters: dict[str, int] = collections.Counter()
    for p in sorted(glob.glob(str(EXP09_RATINGS / "*__native_main_*.csv"))):
        with open(p, newline="") as f:
            for row in csv.DictReader(f):
                rid = (row.get("rater_id") or "").strip()
                if rid == "A1":
                    continue
                val = (row.get("final_score_0_5") or "").strip()
                if val in {"0", "1", "2", "3", "4", "5"}:
                    new_ratings_by_item[row["item_id"]].append(int(val))
                    active_raters[rid] += 1

    assert len(new_ratings_by_item) == 100
    total_new = sum(len(v) for v in new_ratings_by_item.values())
    assert total_new == 250, f"Expected 250 live ratings, got {total_new}"
    assert all(len(v) >= 2 for v in new_ratings_by_item.values())

    # Preserve exact Exp 27 new splits
    exp27_new = {r["item"]: r for r in csv.DictReader((EXP27_DATA / "human_ratings_new_11-24-2026.csv").open())}
    assert len(exp27_new) == 100

    # 3. Build deterministic stratified 5-fold grouped task split (5 old + 5 new tasks per fold)
    old_tasks = sorted({r["task"] for r in old_rows})
    new_tasks = sorted({itemmap[it]["task"] for it in itemmap})
    assert len(old_tasks) == 25 and len(new_tasks) == 25
    assert set(old_tasks).isdisjoint(set(new_tasks))

    rng = np.random.default_rng(SEED_CV5)
    old_perm = [old_tasks[i] for i in rng.permutation(len(old_tasks))]
    new_perm = [new_tasks[i] for i in rng.permutation(len(new_tasks))]
    cv5_of: dict[tuple[str, str], int] = {}
    for fold in range(5):
        for t in old_perm[fold * 5:(fold + 1) * 5]:
            cv5_of[("old", t)] = fold
        for t in new_perm[fold * 5:(fold + 1) * 5]:
            cv5_of[("new", t)] = fold

    # Write anonymised human_ratings_old_11-26-2026.csv & human_ratings_new_11-26-2026.csv
    with (OUT_DIR / "human_ratings_old_11-26-2026.csv").open("w", newline="") as f:
        w = csv.writer(f, lineterminator="\n")
        w.writerow(["item", "task", "set", "exp27_split", "cv5_fold", "n_ratings", "ratings_sorted_0to5_rater_identity_removed", "freeze"])
        for r in old_rows:
            w.writerow([
                r["item"], r["task"], "old", r["split"], cv5_of[("old", r["task"])],
                r["n_ratings"], r["ratings_sorted_0to5_rater_identity_removed"],
                "exp 100 / exp 21 / exp 27 expert ratings, frozen earlier",
            ])

    with (OUT_DIR / "human_ratings_new_11-26-2026.csv").open("w", newline="") as f:
        w = csv.writer(f, lineterminator="\n")
        w.writerow(["item", "task", "set", "exp27_split", "cv5_fold", "n_ratings", "ratings_sorted_0to5_rater_identity_removed", "freeze"])
        for it in sorted(itemmap):
            task = itemmap[it]["task"]
            rats = sorted(new_ratings_by_item[it])
            e27 = exp27_new[it]
            assert e27["task"] == task
            w.writerow([
                it, task, "new", e27["split"], cv5_of[("new", task)],
                len(rats), " ".join(map(str, rats)),
                "Thu 11-26-2026 15:47 PST (Exp 09 live 250 ratings; T30 verified 0/100)",
            ])

    # Write task_splits_11-26-2026.csv
    exp27_task_split = {}
    for r in old_rows:
        exp27_task_split[("old", r["task"])] = r["split"]
    for it, r in exp27_new.items():
        exp27_task_split[("new", r["task"])] = r["split"]

    with (OUT_DIR / "task_splits_11-26-2026.csv").open("w", newline="") as f:
        w = csv.writer(f, lineterminator="\n")
        w.writerow(["task", "set", "exp27_split", "cv5_fold", "how_assigned"])
        for s in ("old", "new"):
            tasks = old_tasks if s == "old" else new_tasks
            for t in tasks:
                w.writerow([
                    t, s, exp27_task_split[(s, t)], cv5_of[(s, t)],
                    f"exp27_split from exp27 data_11-24-2026; cv5_fold stratified 5-fold via default_rng({SEED_CV5})",
                ])

    # 4. Copy judge_scores_h2_11-26-2026.csv & edit_distance_feature_11-26-2026.csv cleanly
    (OUT_DIR / "judge_scores_h2_11-26-2026.csv").write_text((EXP27_DATA / "judge_scores_h2_11-24-2026.csv").read_text())
    (OUT_DIR / "edit_distance_feature_11-26-2026.csv").write_text((EXP27_DATA / "edit_distance_feature_11-24-2026.csv").read_text())

    # 5. Parse all 175 H3 Astra cached responses (including A/B/C/D/base_score/confidence)
    h3_rows = {}
    for fn in ("h3_trainval_vals_codex.jsonl", "h3_test_vals_codex.jsonl"):
        for line in (CACHE_DIR / fn).open():
            obj = json.loads(line)
            if obj.get("status") != "ok":
                continue
            it = obj["id"].split("#r")[0]
            h3_rows[it] = parse_h3_json(obj["raw_response"])
    assert len(h3_rows) == 175, f"Expected 175 H3 rows, got {len(h3_rows)}"

    all_items = [r["item"] for r in old_rows] + sorted(itemmap)
    with (OUT_DIR / "h3_features_astra_11-26-2026.csv").open("w", newline="") as f:
        w = csv.writer(f, lineterminator="\n")
        w.writerow(["item", "h3_score", "p0", "p1", "p2", "p3", "p4", "p5", "A", "B", "C", "D", "base_score", "confidence"])
        for it in all_items:
            h = h3_rows[it]
            w.writerow([
                it, h["h3_score"], *[round(x, 6) for x in h["probs"]],
                h["A"], h["B"], h["C"], h["D"], h["base_score"], h["confidence"],
            ])

    print(f"Wrote {OUT_DIR}: old=75 (195 ratings), new=100 ({total_new} ratings, min_per_item={min(len(v) for v in new_ratings_by_item.values())}), H3=175.")


if __name__ == "__main__":
    main()
