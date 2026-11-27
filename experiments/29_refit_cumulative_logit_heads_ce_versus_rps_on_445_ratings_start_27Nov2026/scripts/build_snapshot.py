#!/usr/bin/env python3
"""Build the 11-27-2026 anonymised snapshot from ratings already in the repo.

Joins each main-round score on (rater_id, item_id). Does not read candidate_file
as a key. Experiment 09 records one inspected edit: rater T06 wrote free text into
candidate_file on native-heavy-11-11-2026__item020. That row is kept because its
item_id is intact. Rater names are not written. Old expert ratings are copied from
the experiment 28 anonymised file, which copied experiment 27.
"""
from __future__ import annotations

import collections
import csv
import hashlib
import json
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[3]
EXP = Path(__file__).resolve().parents[1]
EXP09 = ROOT / "experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/ratings"
EXP28 = ROOT / "experiments/28_multi_family_distributional_judge_and_open_weight_lora_on_new_ratings_start_26Nov2026"
EXP27 = ROOT / "experiments/27_build_a_judge_that_beats_the_constant_forecast_on_held_out_tasks_old_new_ratings_start_24Nov2026/data_11-24-2026"
OUT = EXP / "data_11-27-2026"
VALID = {"0", "1", "2", "3", "4", "5"}
SCHEMA_ATTEST = {"yes", "no", "unsure"}
KNOWN_ANOMALY = ("T06", "native-heavy-11-11-2026__item020")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_csv(path: Path):
    with path.open(newline="") as handle:
        return list(csv.DictReader(handle))


def canonical_candidate(rows_for_item):
    paths = [r["candidate_file"] for r in rows_for_item if r["candidate_file"].endswith(".lean")]
    if not paths:
        raise RuntimeError("no canonical candidate path")
    return collections.Counter(paths).most_common(1)[0][0]


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    exp28_new = {r["item"]: r for r in read_csv(EXP28 / "data_11-26-2026/human_ratings_new_11-26-2026.csv")}
    exp28_old = read_csv(EXP28 / "data_11-26-2026/human_ratings_old_11-26-2026.csv")
    splits = {(r["set"], r["task"]): r for r in read_csv(EXP28 / "data_11-26-2026/task_splits_11-26-2026.csv")}
    assert len(exp28_new) == 100 and len(exp28_old) == 75 and len(splits) == 50

    by_item = collections.defaultdict(list)
    att_counts = collections.Counter()
    rater_counts = collections.Counter()
    blank_rater_counts = collections.Counter()
    anomalies = []
    seen = set()
    for path in sorted(EXP09.glob("*__native_main_*.csv")):
        for row in read_csv(path):
            rid = (row.get("rater_id") or "").strip()
            if rid == "A1":
                continue
            score = (row.get("final_score_0_5") or "").strip()
            if score not in VALID:
                continue
            item = (row.get("item_id") or "").strip()
            key = (rid, item)
            if key in seen:
                raise RuntimeError(f"duplicate rating key {key}")
            seen.add(key)
            att_key = "ai_assisted_rating_attestation (AI help is allowed)"
            att = (row.get(att_key) or "").strip()
            label = att if att else "blank"
            if label not in ("yes", "partial", "blank"):
                label = "other:" + label
            att_counts[label] += 1
            rater_counts[rid] += 1
            if label == "blank":
                blank_rater_counts[rid] += 1
            by_item[item].append({
                "rater_id": rid,
                "score": int(score),
                "attestation": label,
                "candidate_file": row.get("candidate_file") or "",
                "task_folder": row.get("task_folder") or "",
            })

    assert sum(att_counts.values()) == 250, att_counts
    assert set(by_item) == set(exp28_new)
    assert all(len(v) >= 2 for v in by_item.values())

    # Candidate-file audit. The join never uses this column.
    n_noncanonical = 0
    for item, rows in by_item.items():
        canon = canonical_candidate(rows)
        for row in rows:
            if row["candidate_file"] != canon:
                n_noncanonical += 1
                anomalies.append({
                    "item": item,
                    "rater_id": row["rater_id"],
                    "candidate_file_is_lean_path": row["candidate_file"].endswith(".lean"),
                    "score": row["score"],
                    "known_inspected_edit": (row["rater_id"], item) == KNOWN_ANOMALY,
                })
    assert n_noncanonical == 1, anomalies
    assert anomalies[0]["known_inspected_edit"] and anomalies[0]["score"] == 5
    item020 = by_item["native-heavy-11-11-2026__item020"]
    assert sorted(r["score"] for r in item020) == [5, 5, 5]
    assert len(item020) == 3

    def ratings_for(item, mode):
        rows = by_item[item]
        if mode == "all":
            kept = rows
        elif mode == "drop_blank":
            kept = [r for r in rows if r["attestation"] != "blank"]
        elif mode == "schema_yes_no_unsure":
            kept = [r for r in rows if r["attestation"] in SCHEMA_ATTEST]
        else:
            raise ValueError(mode)
        return sorted(r["score"] for r in kept)

    # The all-scores multiset must match the experiment 28 freeze, artifact by artifact.
    for item, prev in exp28_new.items():
        got = " ".join(map(str, ratings_for(item, "all")))
        if got != prev["ratings_sorted_0to5_rater_identity_removed"]:
            raise RuntimeError(f"histogram mismatch {item}: {got} vs {prev['ratings_sorted_0to5_rater_identity_removed']}")

    h2_scores = collections.defaultdict(lambda: collections.defaultdict(list))
    for row in read_csv(EXP28 / "data_11-26-2026/judge_scores_h2_11-26-2026.csv"):
        h2_scores[row["item"]][row["judge"]].append(int(row["score_0to5"]))
    h3 = {r["item"]: r for r in read_csv(EXP28 / "data_11-26-2026/h3_features_astra_11-26-2026.csv")}
    struct = {r["item"]: r for r in read_csv(EXP28 / "data_11-26-2026/structural_features_11-26-2026.csv")}
    edit = {r["item"]: r for r in read_csv(EXP28 / "data_11-26-2026/edit_distance_feature_11-26-2026.csv")}

    def load_h4(name):
        out = {}
        path = EXP28 / "results" / name
        with path.open() as handle:
            for line in handle:
                obj = json.loads(line)
                if obj["status"] != "ok":
                    raise RuntimeError(f"{name} {obj['id']} status {obj['status']}")
                probs = [float(x) for x in obj["parsed"]["probs"]]
                if len(probs) != 6 or min(probs) < 0 or abs(sum(probs) - 1) > 0.05:
                    raise RuntimeError(f"bad H4 probs {obj['id']}")
                probs = [p / sum(probs) for p in probs]
                out[obj["id"]] = {
                    "expected": float(obj["parsed"]["expected_score"]),
                    "probs": probs,
                }
        return out

    h4 = {
        "astra": load_h4("h4_codex_astra_11-26-2026.jsonl"),
        "argon": load_h4("h4_agy_argon_11-26-2026.jsonl"),
        "opus": load_h4("h4_agy_opus_11-26-2026.jsonl"),
    }

    items = [r["item"] for r in exp28_old] + sorted(exp28_new)
    assert len(items) == 175
    for item in items:
        assert item in h2_scores and "H2_astra" in h2_scores[item] and "H2_opus" in h2_scores[item]
        assert item in h3 and item in struct and item in edit
        assert item in h4["astra"] and item in h4["argon"] and item in h4["opus"]

    header = [
        "item", "task", "set", "split", "cv5_fold",
        "n_all", "ratings_all", "n_drop_blank", "ratings_drop_blank",
        "n_schema", "ratings_schema",
        "astra", "opus", "h3_score", "h3_expected",
        "h4_astra", "h4_argon", "h4_opus",
        "thm_ratio", "excess_thm_log", "ident_jaccard", "edit_similarity",
    ]
    for prefix in ("h2", "h3", "h4_astra", "h4_argon", "h4_opus"):
        header += [f"{prefix}_p{k}" for k in range(6)]

    n_drop_changed = 0
    n_schema_empty = 0
    with (OUT / "artifacts_11-27-2026.csv").open("w", newline="") as handle:
        writer = csv.writer(handle, lineterminator="\n")
        writer.writerow(header)
        for item in items:
            if item in exp28_new:
                meta = exp28_new[item]
                task, cohort, split = meta["task"], "new", meta["exp27_split"]
                fold = meta["cv5_fold"]
                all_r = ratings_for(item, "all")
                drop_r = ratings_for(item, "drop_blank")
                schema_r = ratings_for(item, "schema_yes_no_unsure")
                if drop_r != all_r:
                    n_drop_changed += 1
                if not schema_r:
                    n_schema_empty += 1
            else:
                meta = next(r for r in exp28_old if r["item"] == item)
                task, cohort, split = meta["task"], "old", meta["exp27_split"]
                fold = meta["cv5_fold"]
                all_r = [int(x) for x in meta["ratings_sorted_0to5_rater_identity_removed"].split()]
                drop_r, schema_r = list(all_r), list(all_r)
            h3_probs = [float(h3[item][f"p{k}"]) for k in range(6)]
            h3_expected = float(np.dot(h3_probs, np.arange(6)))
            h2_counts = np.bincount(h2_scores[item]["H2_astra"] + h2_scores[item]["H2_opus"], minlength=6).astype(float)
            h2_probs = (h2_counts / h2_counts.sum()).tolist()
            row = [
                item, task, cohort, split, fold,
                len(all_r), " ".join(map(str, all_r)),
                len(drop_r), " ".join(map(str, drop_r)),
                len(schema_r), " ".join(map(str, schema_r)),
                float(np.mean(h2_scores[item]["H2_astra"])),
                float(np.mean(h2_scores[item]["H2_opus"])),
                int(h3[item]["h3_score"]), h3_expected,
                h4["astra"][item]["expected"], h4["argon"][item]["expected"], h4["opus"][item]["expected"],
                float(struct[item]["thm_ratio"]), float(struct[item]["excess_thm_log"]),
                float(struct[item]["ident_jaccard"]), float(edit[item]["edit_similarity"]),
            ]
            row += h2_probs
            row += h3_probs
            row += h4["astra"][item]["probs"]
            row += h4["argon"][item]["probs"]
            row += h4["opus"][item]["probs"]
            writer.writerow(row)

    blank_sizes = sorted(blank_rater_counts.values(), reverse=True)
    audit = {
        "date": "11-27-2026",
        "join_key": ["rater_id", "item_id"],
        "candidate_file_not_used_as_key": True,
        "n_new_numeric_ratings": 250,
        "n_old_ratings": 195,
        "n_artifacts": 175,
        "n_tasks": 50,
        "new_score_counts": dict(collections.Counter(r["score"] for rows in by_item.values() for r in rows)),
        "new_percent_fives": 185 / 250,
        "attestation_counts_on_250_scored_rows": dict(att_counts),
        "blank_attestation_row_counts_per_rater_id_descending": blank_sizes,
        "rater_ids_with_a_numeric_score": sorted(rater_counts),
        "ratings_per_rater_id": dict(rater_counts),
        "candidate_file_anomalies": anomalies,
        "item020_scores_via_item_id": [5, 5, 5],
        "item020_histogram_unchanged_if_anomalous_row_dropped": True,
        "n_new_artifacts_whose_multiset_changes_if_blank_attestations_drop": n_drop_changed,
        "n_new_artifacts_with_zero_schema_attestations": n_schema_empty,
        "matches_experiment_28_all_score_histograms": True,
        "source_sha256": {
            "exp28_new_ratings": sha256(EXP28 / "data_11-26-2026/human_ratings_new_11-26-2026.csv"),
            "exp28_old_ratings": sha256(EXP28 / "data_11-26-2026/human_ratings_old_11-26-2026.csv"),
            "exp28_h2": sha256(EXP28 / "data_11-26-2026/judge_scores_h2_11-26-2026.csv"),
            "exp28_h3": sha256(EXP28 / "data_11-26-2026/h3_features_astra_11-26-2026.csv"),
            "exp27_h2": sha256(EXP27 / "judge_scores_h2_11-24-2026.csv"),
        },
        "note": "Rater names are not stored. rater_id values are the public roster keys already in experiment 09. Blank-attestation counts are aggregated.",
    }
    (OUT / "join_audit_11-27-2026.json").write_text(json.dumps(audit, indent=2) + "\n")
    print(json.dumps({k: audit[k] for k in (
        "n_new_numeric_ratings", "new_percent_fives", "attestation_counts_on_250_scored_rows",
        "candidate_file_anomalies", "n_new_artifacts_whose_multiset_changes_if_blank_attestations_drop",
        "n_new_artifacts_with_zero_schema_attestations", "matches_experiment_28_all_score_histograms",
    )}, indent=2))


if __name__ == "__main__":
    main()
