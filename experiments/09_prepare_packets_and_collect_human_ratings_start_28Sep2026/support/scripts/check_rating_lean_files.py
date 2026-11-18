"""Compile every Lean file of the rating packet with the packet's own Lean project (Lean/Mathlib v4.22.0).

Run from anywhere after `lake exe cache get && lake build` in rating_task_packet/main_rating_task/:
    python3 support/scripts/check_rating_lean_files.py [--jobs 6]
Writes support/LEAN_COMPILE_STATUS_MAIN_PACKET.json (one row per file: compiles yes/no, first error line).
Exit code 1 only if a gold reference fails: references must compile; agent files are rated as written, so their
proof failures are recorded, not fixed (FSC rates theorem statements, not proofs).
"""
from __future__ import annotations

import argparse
import concurrent.futures as cf
import hashlib
import json
import subprocess
import sys
from pathlib import Path

EXPERIMENT = Path(__file__).resolve().parents[2]
PROJECT = EXPERIMENT / "rating_task_packet/main_rating_task"
OUT = EXPERIMENT / "support/LEAN_COMPILE_STATUS_MAIN_PACKET.json"


def check(path: Path) -> dict:
    proc = subprocess.run(["lake", "env", "lean", str(path.relative_to(PROJECT))], cwd=PROJECT,
                          capture_output=True, text=True, timeout=600)
    errors = [line for line in (proc.stdout + proc.stderr).splitlines() if ": error" in line]
    return {"file": str(path.relative_to(PROJECT)), "role": "reference" if "gold_lean" in path.parts else "agent",
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(), "compiles": proc.returncode == 0,
            "first_error": errors[0].split(": error", 1)[1].strip()[:200] if errors else ""}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--jobs", type=int, default=6)
    args = parser.parse_args()
    files = sorted(PROJECT.glob("task_*/*_lean/*.lean"))
    with cf.ThreadPoolExecutor(args.jobs) as pool:
        rows = list(pool.map(check, files))
    toolchain = (PROJECT / "lean-toolchain").read_text().strip()
    summary = {"toolchain": toolchain, "files": len(rows), "compile": sum(r["compiles"] for r in rows),
               "references_failing": [r["file"] for r in rows if r["role"] == "reference" and not r["compiles"]],
               "agent_files_failing": [r["file"] for r in rows if r["role"] == "agent" and not r["compiles"]]}
    OUT.write_text(json.dumps({"summary": summary, "rows": rows}, indent=1) + "\n")
    print(json.dumps(summary, indent=1))
    return 1 if summary["references_failing"] else 0


if __name__ == "__main__":
    sys.exit(main())
