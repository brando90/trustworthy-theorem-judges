#!/usr/bin/env python3
"""TLDR: Reproduce post hoc task-bootstrap error intervals from hash-checked private historical data, exporting aggregate results only."""
from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
from pathlib import Path
import subprocess

import numpy as np

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-repo", type=Path, required=True)
    args = parser.parse_args()
    manifest = json.loads((ROOT / "SOURCE_MANIFEST.json").read_text())
    source = manifest["source_files"]["cv_items"]
    data = subprocess.check_output(
        ["git", "show", manifest["source_commit"] + ":" + source["path"]],
        cwd=args.source_repo,
    )
    assert hashlib.sha256(data).hexdigest() == source["sha256"]
    rows = [r for r in csv.DictReader(io.StringIO(data.decode())) if r["e100_split"] == "test"]
    target_source = manifest["source_files"]["items"]
    target_data = subprocess.check_output(
        ["git", "show", manifest["source_commit"] + ":" + target_source["path"]],
        cwd=args.source_repo,
    )
    assert hashlib.sha256(target_data).hexdigest() == target_source["sha256"]
    targets = {r["item"]: r for r in (json.loads(line) for line in target_data.splitlines() if line.strip())}
    # The old CSV rounded human targets; use the full-precision frozen targets.
    for row in rows:
        original = targets[row["item"]]
        assert original["split"] == "test" and original["task"] == row["task"]
        row["target_expert"] = original["target_expert"]
    receipt = json.loads((ROOT / "exp100_TEST_RECEIPT.json").read_text())
    result = {
        "description": "Post hoc supplement computed 11-06-2026 from frozen historical data; no new human ratings or model calls; original receipt unchanged.",
        "source_commit": manifest["source_commit"],
        "source_sha256": source["sha256"],
        "target_source_sha256": target_source["sha256"],
        "method": "95% percentile bootstrap sampling whole tasks with replacement; each sampled task retains all its candidates; seed 20260928, matching the original metric code.",
        "mean_bias_definition": "judge minus available-expert mean; positive means more lenient",
        "p_value": "n/a; descriptive intervals, no hypothesis test",
        "source_data_publication": "Aggregate statistics only; no per-item or individual human ratings included.",
        "subsets": {},
    }
    for name, subset, draws in [
        ("all_items", rows, 10000),
        ("ordinary_items", [r for r in rows if r["placeholder"].strip().lower() in ("false", "0")], 2000),
    ]:
        task_ids = sorted({r["task"] for r in subset})
        expected = receipt[name]
        assert len(subset) == expected["n_items"]
        assert len(task_ids) == expected["n_tasks"]
        pred = np.array([float(r["e100_frozen_judge"]) for r in subset])
        human = np.array([float(r["target_expert"]) for r in subset])
        error = pred - human
        values = {"mae": float(np.abs(error).mean()), "mean_bias": float(error.mean())}
        assert np.isclose(values["mae"], expected["mae"], rtol=0, atol=1e-12)
        assert np.isclose(pred.mean(), expected["mean_pred"], rtol=0, atol=1e-12)
        assert np.isclose(human.mean(), expected["mean_target"], rtol=0, atol=1e-12)
        positions = {t: np.array([i for i, r in enumerate(subset) if r["task"] == t]) for t in task_ids}
        rng = np.random.default_rng(20260928)
        boot = {"mae": [], "mean_bias": []}
        for _ in range(draws):
            picked = rng.integers(0, len(task_ids), len(task_ids))
            index = np.concatenate([positions[task_ids[i]] for i in picked])
            boot["mae"].append(float(np.abs(error[index]).mean()))
            boot["mean_bias"].append(float(error[index].mean()))
        result["subsets"][name] = {
            "n_items": len(subset),
            "n_tasks": len(task_ids),
            "bootstrap_draws": draws,
            "mean_judge": float(pred.mean()),
            "mean_expert": float(human.mean()),
            "metrics": {
                k: {"value": values[k], "lo": float(np.percentile(v, 2.5)), "hi": float(np.percentile(v, 97.5))}
                for k, v in boot.items()
            },
        }
    output = ROOT / "POSTHOC_ERROR_INTERVALS_11-06-2026.json"
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result["subsets"], indent=2))


if __name__ == "__main__":
    main()
