#!/usr/bin/env python3
"""TLDR: Recompute agreement between the GPT-5.3-Codex human-rubric judge (VeriBench experiment 58) and the pooled human target, with 95% task-bootstrap intervals, from hash-checked private data; exports aggregates only."""
from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
from pathlib import Path
import subprocess

import numpy as np
from scipy import stats

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "POSTHOC_CLI_RUBRIC_JUDGE_AGREEMENT_11-12-2026.json"
SEED = 20261112
DRAWS = 10000
GROUP_ROWS = (
    "lenient_set",
    "expert_harsh_set",
    "five_independent_no_old_prompt_repeat",
    "all7_available",
    "participant1_correct",
    "participant2",
    "participant3",
    "participant4",
    "participant5",
    "old_pass1",
    "old_pass2",
)


def read_source(source_repo: Path, commit: str, entry: dict) -> bytes:
    data = subprocess.check_output(["git", "show", f"{commit}:{entry['path']}"], cwd=source_repo)
    assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]
    if "git_blob" in entry:
        blob = subprocess.check_output(["git", "rev-parse", f"{commit}:{entry['path']}"], cwd=source_repo, text=True).strip()
        assert blob == entry["git_blob"], entry["path"]
    return data


def icc(judge: np.ndarray, human: np.ndarray) -> tuple[float, float]:
    """Two-way single-score ICC(A,1) (Shrout-Fleiss ICC(2,1)) and ICC(C,1) (ICC(3,1)), McGraw and Wong 1996."""
    y = np.column_stack([judge, human])
    n, k = y.shape
    grand = y.mean()
    ss_rows = k * ((y.mean(axis=1) - grand) ** 2).sum()
    ss_cols = n * ((y.mean(axis=0) - grand) ** 2).sum()
    ss_error = ((y - grand) ** 2).sum() - ss_rows - ss_cols
    ms_rows = ss_rows / (n - 1)
    ms_cols = ss_cols / (k - 1)
    ms_error = ss_error / ((n - 1) * (k - 1))
    consistency = (ms_rows - ms_error) / (ms_rows + (k - 1) * ms_error)
    absolute = (ms_rows - ms_error) / (ms_rows + (k - 1) * ms_error + k * (ms_cols - ms_error) / n)
    return float(absolute), float(consistency)


def correlations(judge: np.ndarray, human: np.ndarray) -> dict[str, float]:
    if np.ptp(judge) == 0 or np.ptp(human) == 0:
        return {"pearson_r": np.nan, "spearman_rho": np.nan, "kendall_tau_b": np.nan}
    return {
        "pearson_r": float(stats.pearsonr(judge, human)[0]),
        "spearman_rho": float(stats.spearmanr(judge, human)[0]),
        "kendall_tau_b": float(stats.kendalltau(judge, human)[0]),
    }


def item_level(judge: np.ndarray, human: np.ndarray) -> dict[str, float]:
    values = correlations(judge, human)
    error = judge - human
    absolute, consistency = icc(judge, human)
    values.update({
        "mean_judge": float(judge.mean()),
        "mean_human": float(human.mean()),
        "mean_bias": float(error.mean()),
        "mean_absolute_error": float(np.abs(error).mean()),
        "icc_a1": absolute,
        "icc_c1": consistency,
        "pearson_minus_spearman": values["pearson_r"] - values["spearman_rho"],
    })
    return values


def task_means(judge: np.ndarray, human: np.ndarray, groups: list[np.ndarray]) -> dict[str, float]:
    return correlations(np.array([judge[g].mean() for g in groups]), np.array([human[g].mean() for g in groups]))


def within_task(judge: np.ndarray, human: np.ndarray, groups: list[np.ndarray]) -> dict[str, float]:
    centered_judge = np.concatenate([judge[g] - judge[g].mean() for g in groups])
    centered_human = np.concatenate([human[g] - human[g].mean() for g in groups])
    values = correlations(centered_judge, centered_human)
    return {"pearson_r": values["pearson_r"], "spearman_rho": values["spearman_rho"]}


def is_true(value: object) -> bool:
    assert value in (True, False, "True", "False"), value
    return value in (True, "True")


def interval(draws: list[float]) -> dict[str, float | int]:
    finite = np.array([d for d in draws if np.isfinite(d)])
    return {"lo": float(np.percentile(finite, 2.5)), "hi": float(np.percentile(finite, 97.5)), "valid_draws": int(finite.size)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-repo", type=Path, required=True)
    args = parser.parse_args()
    manifest = json.loads((ROOT / "SOURCE_MANIFEST.json").read_text())
    commit = manifest["source_commit"]
    files = manifest["source_files"]
    items = list(csv.DictReader(io.StringIO(read_source(args.source_repo, commit, files["cli_judge_items"]).decode())))
    receipt = json.loads(read_source(args.source_repo, commit, files["cli_judge_metrics"]))
    groups_table = {r["label_group"]: r for r in csv.DictReader(io.StringIO(read_source(args.source_repo, commit, files["cli_judge_label_groups"]).decode()))}

    assert len(items) == receipt["n_label_items_scored"] == 75
    assert all(r["api_error"] == "" for r in items), "receipt rows must be complete"
    tasks = sorted({r["task_key"] for r in items})
    assert len(tasks) == 25
    positions = [np.array([i for i, r in enumerate(items) if r["task_key"] == t]) for t in tasks]
    assert all(len(p) == 3 for p in positions)
    human = np.array([float(r["human_score_0_5"]) for r in items])
    scorers = {
        "raw": np.array([float(r["raw_score_0_5"]) for r in items]),
        "isotonic_two_fold_task_split": np.array([float(r["isotonic_oof_pred_0_5"]) for r in items]),
    }
    receipt_keys = {"raw": "raw_zero_shot_all_available_avg", "isotonic_two_fold_task_split": "cv2_task_split_isotonic_all_available_avg"}

    result = {
        "description": "Post hoc supplement computed 11-12-2026 from frozen historical data; no new human ratings or model calls; original receipts unchanged.",
        "source_commit": commit,
        "judge": "gpt-5.3-codex through codex exec, model_reasoning_effort xhigh, human rating prompt over full Python, reference Lean and candidate Lean files, mean of 3 calls per item (VeriBench experiment 58, run committed 05-20-2026 at daaa09451a2361463ebd6cbcc7afbf3aa9354ec7)",
        "target": "human_score_0_5: per-item mean of all available ratings in the seven pooled rating files (five raters; one rater's two earlier-prompt passes included), 0-5 scale",
        "scale": "0-5; mean bias is judge minus human, positive means the judge is more lenient",
        "method": f"95% percentile bootstrap sampling whole tasks with replacement (each task keeps its three candidates); {DRAWS} draws; seed {SEED}. Isotonic out-of-fold predictions are held fixed, so their intervals condition on the two fitted fold mappings.",
        "icc_definitions": "ICC(A,1) two-way absolute agreement single score (Shrout-Fleiss ICC(2,1)); ICC(C,1) two-way consistency single score (ICC(3,1)); judge and pooled human mean as the two columns",
        "p_values": "Receipt p-values test zero association and treat the 75 items as independent, ignoring task clustering; bootstrap intervals are descriptive (p-val=n/a).",
        "source_data_publication": "Aggregate statistics only; no per-item or individual human ratings included.",
        "n_items": len(items),
        "n_tasks": len(tasks),
        "item_level": {},
        "receipt_p_values": {},
    }
    rng = np.random.default_rng(SEED)
    picks = [rng.integers(0, len(tasks), len(tasks)) for _ in range(DRAWS)]

    for name, judge in scorers.items():
        point = item_level(judge, human)
        stored = receipt[receipt_keys[name]]
        for ours, theirs in (("pearson_r", "pearson_r"), ("spearman_rho", "spearman_rho"), ("kendall_tau_b", "kendall_tau")):
            assert abs(point[ours] - stored[theirs]) < 1e-12, (name, ours)
        result["receipt_p_values"][name] = {k: stored[k] for k in ("pearson_p", "spearman_p", "kendall_p")}
        boot: dict[str, list[float]] = {k: [] for k in point}
        for picked in picks:
            index = np.concatenate([positions[i] for i in picked])
            for k, v in item_level(judge[index], human[index]).items():
                boot[k].append(v)
        result["item_level"][name] = {k: {"value": point[k], **interval(boot[k])} for k in point}

    # Reference-quality subsets: join rating-era reference flags from the pinned experiment 100 item manifest.
    manifest_items = {
        f"{r['gold_file_name']}::{r['candidate_file']}": r
        for r in (json.loads(line) for line in read_source(args.source_repo, commit, files["items"]).splitlines() if line.strip())
    }
    assert len(manifest_items) == 75 and all(r["item_key"] in manifest_items for r in items)
    flags = [manifest_items[r["item_key"]] for r in items]
    raw = scorers["raw"]

    # Byte-level input audit: which reference and candidate bytes were in the judge run's committed dataset.
    audit_spec = manifest["judge_inputs"]
    run_commit = audit_spec["run_commit"]
    tree = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", run_commit], cwd=args.source_repo, text=True).splitlines()

    def run_files(root: str) -> dict[str, list[str]]:
        found: dict[str, list[str]] = {}
        for path in tree:
            if path.startswith(root) and path.endswith(".lean"):
                found.setdefault(path.rsplit("/", 1)[1], []).append(path)
        return found

    def run_sha(path: str) -> str:
        return hashlib.sha256(subprocess.check_output(["git", "show", f"{run_commit}:{path}"], cwd=args.source_repo)).hexdigest()

    references, candidates = run_files(audit_spec["reference_root"]), run_files(audit_spec["candidate_root"])
    reference_version, candidate_match = [], []
    for f in flags:
        # The run resolved each reference by file name, preferring the shallowest path.
        path = sorted(references[f["gold_file_name"]], key=lambda p: (p.count("/"), p))[0]
        digest = run_sha(path)
        reference_version.append("rating_era" if digest == f["ref_ann_sha256"] else "later_snapshot" if digest == f["ref_snap_sha256"] else "other")
        candidate_match.append(run_sha(sorted(candidates[f["candidate_file"]])[0]) == f["candidate_sha256"])
    statements_match = [
        v == "rating_era" or (v == "later_snapshot" and f["ref_status"] == "statements_identical")
        for v, f in zip(reference_version, flags)
    ]
    counts: dict[str, int] = {}
    for v, f, m in zip(reference_version, flags, statements_match):
        key = f"{v} | annotation-vs-snapshot {f['ref_status']} | placeholder {is_true(f['ref_placeholder_at_annotation'])} | changed in rating window {is_true(f['ref_ambiguous_in_window'])} | statements match {m}"
        counts[key] = counts.get(key, 0) + 1
    result["input_audit"] = {
        "note": "Compares the files in the judge run's commit with the rating-era hashes in the pinned item manifest; the run read its working tree at run time, which the commit is the best available record of.",
        "run_commit": run_commit,
        "candidates_byte_identical_to_rating_era": int(sum(candidate_match)),
        "artifacts_by_reference_version": {k: counts[k] for k in sorted(counts)},
        "artifacts_with_rating_era_reference_statements": int(sum(statements_match)),
    }

    result["reference_subsets_raw"] = {}
    for label, keep in (
        ("ordinary_references", [not is_true(f["ref_placeholder_at_annotation"]) for f in flags]),
        ("ordinary_and_unambiguous_references", [not is_true(f["ref_placeholder_at_annotation"]) and not is_true(f["ref_ambiguous_in_window"]) for f in flags]),
        ("judge_reference_statements_match_rating_era", statements_match),
        ("judge_reference_statements_match_and_unchanged_in_window", [m and not is_true(f["ref_ambiguous_in_window"]) for m, f in zip(statements_match, flags)]),
        ("judge_reference_statements_differ_from_rating_era", [not m for m in statements_match]),
    ):
        keep_tasks = [i for i, p in enumerate(positions) if all(keep[j] for j in p)]
        assert all(all(keep[j] for j in positions[i]) or not any(keep[j] for j in positions[i]) for i in range(len(tasks))), "flags must be task-level"
        sub_positions = [positions[i] for i in keep_tasks]
        index = np.concatenate(sub_positions)
        point = item_level(raw[index], human[index])
        boot = {k: [] for k in point}
        sub_rng = np.random.default_rng(SEED)
        for _ in range(DRAWS):
            picked = sub_rng.integers(0, len(sub_positions), len(sub_positions))
            sampled = np.concatenate([sub_positions[i] for i in picked])
            for k, v in item_level(raw[sampled], human[sampled]).items():
                boot[k].append(v)
        result["reference_subsets_raw"][label] = {
            "n_items": int(index.size),
            "n_tasks": len(sub_positions),
            **{k: {"value": point[k], **interval(boot[k])} for k in point},
        }

    # Theorem counts behind the mismatched-reference classification (aggregate counts only).
    mismatched = [i for i, m in enumerate(statements_match) if not m]
    result["input_audit"]["mismatched_artifacts_with_judge_run_theorem_count_different_from_rated"] = int(
        sum(int(items[i]["n_gold_theorems"]) != int(flags[i]["n_ref_theorems_ann"]) for i in mismatched)
    )
    result["input_audit"]["third_version_reference_theorem_counts"] = sorted({
        (int(flags[i]["n_ref_theorems_ann"]), int(items[i]["n_gold_theorems"]), int(flags[i]["n_ref_theorems_snap"]))
        for i in mismatched if reference_version[i] == "other"
    })
    result["input_audit"]["third_version_reference_theorem_counts_order"] = "rated, judge run, later snapshot"

    # Constant-prediction baselines for the absolute-error comparison, with paired task-bootstrap differences.
    folds = np.array([int(r["cv2_fold"]) for r in items])
    other_fold_mean = np.array([human[folds != f].mean() for f in folds])
    constant_error = np.abs(other_fold_mean - human)
    differences = {
        "raw_minus_other_fold_constant": np.abs(raw - human) - constant_error,
        "isotonic_minus_other_fold_constant": np.abs(scorers["isotonic_two_fold_task_split"] - human) - constant_error,
    }
    boot = {k: [] for k in ["other_fold_human_mean", *differences]}
    for picked in picks:
        index = np.concatenate([positions[i] for i in picked])
        boot["other_fold_human_mean"].append(float(constant_error[index].mean()))
        for k, v in differences.items():
            boot[k].append(float(v[index].mean()))
    result["constant_baselines"] = {
        "note": "Mean absolute error of predicting a constant: the pooled human mean of all 75 items (in-sample, optimistic) or the mean of the other two-fold task-split fold (matching the information available to the isotonic remapping). Differences are paired: scorer error minus other-fold constant error on the same draws; negative favors the scorer.",
        "in_sample_human_mean": float(np.abs(human.mean() - human).mean()),
        "other_fold_human_mean": {"value": float(constant_error.mean()), **interval(boot["other_fold_human_mean"])},
        **{k: {"value": float(v.mean()), **interval(boot[k])} for k, v in differences.items()},
    }

    # Why the remapping loses pooled rank order: each fold's map was fitted on the other fold.
    iso = scorers["isotonic_two_fold_task_split"]
    result["isotonic_fold_diagnostics"] = {
        "note": "Each fold's predictions come from the map fitted on the other fold's tasks.",
        **{
            f"fold_{f}": {
                "n_items": int((folds == f).sum()),
                "n_tasks": len({items[i]["task_key"] for i in np.where(folds == f)[0]}),
                "human_mean": float(human[folds == f].mean()),
                "raw_spearman_within_fold": float(stats.spearmanr(raw[folds == f], human[folds == f])[0]),
                "isotonic_spearman_within_fold": float(stats.spearmanr(iso[folds == f], human[folds == f])[0]),
                "isotonic_distinct_values": len(set(iso[folds == f].tolist())),
                "isotonic_mean": float(iso[folds == f].mean()),
            }
            for f in sorted(set(folds.tolist()))
        },
    }

    # Pure within-task ordering: Spearman within each task, averaged over tasks where both scores vary.
    def per_task_spearman(task_groups: list[np.ndarray]) -> float:
        values = [stats.spearmanr(raw[g], human[g])[0] for g in task_groups if np.ptp(raw[g]) > 0 and np.ptp(human[g]) > 0]
        return float(np.mean(values)) if values else np.nan

    eligible = sum(1 for g in positions if np.ptp(raw[g]) > 0 and np.ptp(human[g]) > 0)
    boot_per_task = [per_task_spearman([positions[i] for i in picked]) for picked in picks]
    result["raw_mean_per_task_spearman"] = {
        "value": per_task_spearman(positions),
        **interval(boot_per_task),
        "n_tasks_with_varying_scores": eligible,
        "note": "Spearman correlation of the three artifacts within each task, averaged over tasks where neither the judge nor the human scores are constant; each draw averages over its eligible sampled tasks.",
    }

    for label, function in (("task_means", task_means), ("within_task_centered", within_task)):
        point = function(raw, human, positions)
        boot = {k: [] for k in point}
        for picked in picks:
            sampled = [positions[i] for i in picked]
            index = np.concatenate(sampled)
            offsets = np.cumsum([0] + [len(s) for s in sampled[:-1]])
            regrouped = [np.arange(o, o + len(s)) for o, s in zip(offsets, sampled)]
            for k, v in function(raw[index], human[index], regrouped).items():
                boot[k].append(v)
        result[f"raw_{label}"] = {k: {"value": point[k], **interval(boot[k])} for k in point}
    result["raw_task_means"]["n"] = len(tasks)
    result["raw_within_task_centered"]["note"] = "Scores centered within each task before correlating; removes between-task differences."

    judge_mean = float(raw.mean())
    result["rater_group_targets_from_receipt"] = {
        "note": "Copied from the experiment 58 label-group receipt; point estimates only, no intervals in the source. Group targets: lenient = participant 1 earlier-prompt passes plus participants 4 and 5; expert = participant 1 corrected prompt plus participants 2 and 3; five_independent excludes the earlier-prompt passes. raw_n counts items with a rating in that group.",
        "raw_judge_mean_all_75_items": judge_mean,
        "rows": {
            name: {
                "human_mean": float(groups_table[name]["human_mean"]),
                "raw_n": int(groups_table[name]["raw_n"]),
                "raw_pearson_r": float(groups_table[name]["raw_pearson_r"]),
                "raw_spearman_rho": float(groups_table[name]["raw_spearman_rho"]),
                "raw_kendall_tau": float(groups_table[name]["raw_kendall_tau"]),
                "cv2_pearson_r": float(groups_table[name]["cv2_pearson_r"]),
                "cv2_spearman_rho": float(groups_table[name]["cv2_spearman_rho"]),
                "cv2_kendall_tau": float(groups_table[name]["cv2_kendall_tau"]),
                **({"judge_mean_minus_human_mean": judge_mean - float(groups_table[name]["human_mean"])} if int(groups_table[name]["raw_n"]) == 75 else {}),
            }
            for name in GROUP_ROWS
        },
    }
    # Reconstruct the receipt's targets from the run's rating files; individual ratings stay local.
    rating_files = audit_spec["rating_files"]

    def load_ratings(entry: dict) -> dict[tuple[str, str], float]:
        ratings = {}
        for line in read_source(args.source_repo, run_commit, entry).decode().splitlines()[1:]:
            parts = line.split("\t")
            if len(parts) < 3 or not parts[2].strip():
                continue
            try:
                ratings[(parts[0].strip(), parts[1].strip())] = float(parts[2])
            except ValueError:
                continue
        return ratings

    ratings = {name: load_ratings(entry) for name, entry in rating_files.items()}
    # The per-artifact receipt pools all seven files by artifact file name alone.
    by_artifact: dict[str, list[float]] = {}
    for name in rating_files:
        for (_, artifact), score in ratings[name].items():
            by_artifact.setdefault(artifact, []).append(score)
    assert np.allclose([np.mean(by_artifact[r["candidate_file"]]) for r in items], human, rtol=0, atol=1e-12), "pooled target"
    # The label-group receipt matches rows by reference and artifact file names together.
    judge_by_pair = {(r["label_gold_file"], r["candidate_file"]): float(r["raw_score_0_5"]) for r in items}
    members = {
        "all7_available": list(rating_files),
        "lenient_set": ["old_pass1", "old_pass2", "participant4", "participant5"],
        "expert_harsh_set": ["participant1_correct", "participant2", "participant3"],
        "five_independent_no_old_prompt_repeat": ["participant1_correct", "participant2", "participant3", "participant4", "participant5"],
        **{name: [name] for name in rating_files},
    }
    reconstruction = {}
    for group, names in members.items():
        pairs = [p for p in judge_by_pair if any(p in ratings[n] for n in names)]
        target = np.array([np.mean([ratings[n][p] for n in names if p in ratings[n]]) for p in pairs])
        judge_scores = np.array([judge_by_pair[p] for p in pairs])
        stored = groups_table[group]
        assert len(pairs) == int(stored["raw_n"]), group
        assert abs(target.mean() - float(stored["human_mean"])) < 1e-12, group
        assert abs(stats.pearsonr(judge_scores, target)[0] - float(stored["raw_pearson_r"])) < 1e-12, group
        reconstruction[group] = {
            "n_items": len(pairs),
            "human_mean": float(target.mean()),
            "judge_mean_on_these_items": float(judge_scores.mean()),
            "judge_minus_human_mean": float(judge_scores.mean() - target.mean()),
        }
    result["rater_group_reconstruction"] = {
        "note": "Rebuilt from the run's seven rating files. Rows need a tab-separated numeric score. The per-artifact pooled target (matched by artifact file name) reproduces the receipt exactly; every label-group row (matched by reference and artifact file names) reproduces the receipt's count, human mean and Pearson r to 1e-12. Point estimates only.",
        "per_artifact_pooled_target_reproduced": True,
        "rows": reconstruction,
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n")
    summary = {
        name: {k: round(v["value"], 4) for k, v in result["item_level"][name].items()} for name in scorers
    }
    print(json.dumps(summary, indent=2))
    print(json.dumps({k: result[k] for k in ("raw_task_means", "raw_within_task_centered")}, indent=2))


if __name__ == "__main__":
    main()
