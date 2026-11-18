"""Compile the four original heap-sort rating artifacts without modifying them."""
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import os
import signal
import subprocess
import time

OUT = Path(__file__).resolve().parent
EXPERIMENT = OUT.parents[1]
SOURCE = EXPERIMENT / "veribench_rating_packet_25_tasks_100_files/task_01_heap_sort/agent_lean"
ENV = Path.home() / "veribench/veribench_dataset/lean_src"
TIMEOUT = 180


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(path):
    before = sha(path)
    command = ["lake", "env", "lean", str(path)]
    start = time.monotonic()
    timed_out = False
    with (OUT / f"{path.stem}.log").open("w") as log:
        process = subprocess.Popen(command, cwd=ENV, stdout=log, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        try:
            code = process.wait(timeout=TIMEOUT)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(process.pid, signal.SIGKILL)
            code = process.wait()
    text = (OUT / f"{path.stem}.log").read_text()
    result = {
        "file": str(path.relative_to(EXPERIMENT)), "sha256_before": before,
        "sha256_after": sha(path), "command": command, "exit_code": code,
        "timed_out": timed_out, "seconds": round(time.monotonic() - start, 2),
        "errors": sum(": error:" in line for line in text.splitlines()),
        "warnings": sum(": warning:" in line for line in text.splitlines()),
        "log": f"{path.stem}.log",
    }
    assert result["sha256_before"] == result["sha256_after"], path
    print(json.dumps(result), flush=True)
    return result


if __name__ == "__main__":
    files = sorted(SOURCE.glob("agent_*.lean"))
    assert len(files) == 4
    metadata = {
        "started_utc": datetime.now(timezone.utc).isoformat(), "cwd": str(ENV),
        "toolchain": (ENV / "lean-toolchain").read_text().strip(),
        "lean_version": subprocess.check_output(["lake", "env", "lean", "--version"], cwd=ENV, text=True).strip(),
        "mathlib_commit": subprocess.check_output(["git", "-C", str(ENV / ".lake/packages/mathlib"), "rev-parse", "HEAD"], text=True).strip(),
        "timeout_seconds_per_file": TIMEOUT, "parallelism": 2,
        "scope": "Compilation of unchanged files only; no coverage judgment or differential testing.",
    }
    with ThreadPoolExecutor(max_workers=2) as pool:
        metadata["results"] = list(pool.map(check, files))
    metadata["completed_utc"] = datetime.now(timezone.utc).isoformat()
    (OUT / "results.json").write_text(json.dumps(metadata, indent=2) + "\n")
