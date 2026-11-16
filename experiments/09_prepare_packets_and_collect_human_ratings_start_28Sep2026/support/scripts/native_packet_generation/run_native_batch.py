#!/usr/bin/env python3
"""Run all 25 frozen cells for one native-harness condition, a few at a time, one attempt per cell.

Usage: run_native_batch.py --condition C --credentials D --output-dir O [--concurrency 5] [--only TASK ...]

A task whose output folder already exists is skipped (native_cli_runner refuses to retry a cell);
the summary lists every task's terminal status, stop reason and whether a candidate was captured.
"""
from __future__ import annotations

import argparse
import concurrent.futures as futures
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
RUNNER = HERE / "native_cli_runner.py"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--condition", required=True)
    parser.add_argument("--credentials", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--concurrency", type=int, default=5)
    parser.add_argument("--only", nargs="*")
    args = parser.parse_args()
    condition_path = Path(args.condition).resolve()
    condition = json.loads(condition_path.read_text())
    assert condition["status"] == "FROZEN", "Freeze the condition first"
    runner = Path(condition.get("runner_path") or RUNNER)  # each condition binds an exact runner file
    assert condition["runner_sha256"] == hashlib.sha256(runner.read_bytes()).hexdigest(), "Runner changed since freeze"
    manifest_path = Path(condition["input_manifest_path"])
    manifest = json.loads(manifest_path.read_text())
    tasks = [t["task_id"] for t in manifest["tasks"]]
    if args.only:
        tasks = [t for t in tasks if t in set(args.only)]
    out = Path(args.output_dir).resolve()
    out.mkdir(parents=True, exist_ok=True)
    todo = [t for t in tasks if not (out / t).exists()]
    condition_sha = hashlib.sha256(condition_path.read_bytes()).hexdigest()

    def one(task_id: str) -> dict:
        started = time.time()
        proc = subprocess.run([sys.executable, str(runner), "run", "--manifest", str(manifest_path),
                               "--condition", str(condition_path), "--condition-sha256", condition_sha,
                               "--task-id", task_id, "--output-dir", str(out), "--credentials", args.credentials],
                              capture_output=True, text=True)
        receipt = out / task_id / "receipt.json"
        state = json.loads(receipt.read_text()) if receipt.exists() else {}
        return {"task_id": task_id, "rc": proc.returncode, "wall_s": round(time.time() - started, 1),
                "status": state.get("status"), "stop_reason": state.get("stop_reason"),
                "candidate_bytes": state.get("candidate_bytes"), "models": state.get("actual_models"),
                "egress_denied": state.get("egress_denied"), "stderr_tail": proc.stderr[-400:]}

    print(f"launching {len(todo)} of {len(tasks)} cells, concurrency {args.concurrency}", flush=True)
    results = []
    with futures.ThreadPoolExecutor(max_workers=args.concurrency) as pool:
        for result in pool.map(one, todo):
            results.append(result)
            print(json.dumps({k: result[k] for k in ("task_id", "status", "stop_reason", "candidate_bytes", "wall_s")}),
                  flush=True)
    summary = {"condition": str(condition_path), "condition_sha256": condition_sha, "finished_utc": time.time(),
               "launched": len(todo), "captured": sum(bool(r["candidate_bytes"]) for r in results), "cells": results}
    (out / f"BATCH_SUMMARY_{int(time.time())}.json").write_text(json.dumps(summary, indent=1) + "\n")
    print(f"captured {summary['captured']} of {len(todo)} launched")


if __name__ == "__main__":
    main()
