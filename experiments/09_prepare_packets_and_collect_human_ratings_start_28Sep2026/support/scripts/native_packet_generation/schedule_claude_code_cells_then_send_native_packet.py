#!/usr/bin/env python3
"""Run the 6 remaining Claude Code V3 cells on whichever of Brando's Claude plans can pay for them, then finish the
all-native 100-file packet and email Brando his own copy (NATIVE_ATTEMPTS_AMENDMENT_11-16-2026.json, scheduler_update).

Brando, 11-16-2026: "set up a scheduler so we get what I need?" and "I only want the CC native ones."

Cells. Every minute, probe each plan with a one-line Claude Fable 5.1 request inside the frozen container network and
start a waiting cell on the first plan that answers. The Vals plan runs one cell at a time: its per-user spend limit
allowed about $12-17 of usage per 5-hour window on 11-16-2026, and cells running together were all cut off. Brando's
personal and Stanford plans (usage credits) run every waiting cell at once. A run stopped by billing keeps its folder
and the cell's next attempt takes the next folder; billing stops never count toward the 3 attempts. A cell stopped by
billing although it opened a fresh Vals window does not fit one window, so it waits for another plan.
BILLING_ROUTE.json in each cell folder names the plan. Tokens travel only through the environment.

Finish, once all 6 cells have usable files (each step must succeed before the next): build_native_cohort.py with all
three groups; move the earlier, never-sent build aside; build_full_team_packets.py build, sheets, drafts, review,
send-a1 (Brando's own packet, to Brando only); then export and status. Team emails go out only if
sealed/TEAM_SEND_APPROVED.json records Brando's yes; otherwise they stay unsent Gmail drafts.

Exit 0 once Brando's packet is in his Inbox, 2 if a step fails, 3 if cells are still missing at the deadline.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import build_native_cohort as nc  # noqa: E402  (the cohort builder's own acceptance test decides "usable")

REPO = HERE.parents[4]
N = REPO / "research_artifacts/09_human_rating_collection/preparation_11-09-2026/native_harness_packet_11-11-2026"
SEALED = REPO / "research_artifacts/09_human_rating_collection/preparation_11-09-2026/full_team_11-14-2026/sealed"
RUNNER, COHORT_BUILDER, PACKETS = (HERE / "claude_code_runner.py", HERE / "build_native_cohort.py",
                                   HERE / "build_full_team_packets.py")
KEYS = Path.home() / "keys"
CONDITION = N / "CC_CONDITION_VALID_V3.json"
CONDITION_SHA256 = hashlib.sha256(CONDITION.read_bytes()).hexdigest()
MODEL = json.loads(CONDITION.read_text())["model"]
MANIFEST = N / "inputs_and_existing/INPUT_MANIFEST.json"
TASKS = ["humaneval_set__humaneval_39_prime_fib", "cs_set__topological_sort", "cs_set__heapsort_algorithm",
         "cs_set__edit_distance", "cs_set__heap_sort", "realcode_set__23_base32"]
ROOTS = [N / "claude_code_valid_v3"] + [N / f"claude_code_valid_v3_attempt{k}" for k in range(2, 7)]
VALS = "vals_claude_plan"
PLANS = [(VALS, KEYS / "claude_vals_oauth_token.txt", 1),  # (name, token file, cells at once)
         ("personal_claude_plan", KEYS / "claude_personal_oauth_token.txt", 6),
         ("personal_claude_plan_code_token", KEYS / "claude_code_oauth_token.txt", 6),
         ("stanford_claude_plan", KEYS / "claude_su_oauth_token.txt", 6)]
BILLING_STOPS = ("spend limit", "out of usage credits", "usage credits are required", "hit your limit", "usage limit")
COHORT = SEALED / "RATABLE_COHORT_100_NATIVE.json"
BUILDS, BUILD_INDEX = SEALED / "builds_100_native", SEALED / "BUILD_INDEX_100_NATIVE.json"
TEAM_SEND_APPROVAL = SEALED / "TEAM_SEND_APPROVED.json"
WANTED_COUNTS = {"historical_codex_astra": 25, "native_claude_fable": 19, "native_claude_fable_v3": 6,
                 "native_grok_cli": 25, "native_antigravity_gemini": 25}


def log(message: str) -> None:
    print(time.strftime("%m-%d %H:%M:%S ") + message, flush=True)


class State:
    def __init__(self, path: Path, hours: float):
        self.path = path
        self.data = {"phase": "cells", "started": time.strftime("%m-%d-%Y %H:%M %Z"),
                     "deadline_unix": int(time.time() + hours * 3600), "plans": {}, "cells": {}, "steps": [],
                     "vals_too_small_for": []}

    def save(self) -> None:
        self.data["updated"] = time.strftime("%m-%d-%Y %H:%M:%S %Z")
        self.path.write_text(json.dumps(self.data, indent=1) + "\n")


def probe(token_file: Path) -> tuple[bool, str]:
    """One-line Claude Fable 5.1 request through the same image, network and proxy as the cells."""
    cmd = ["docker", "run", "--rm", "--network", "ttj-native-source-only", "-e", "CLAUDE_CODE_OAUTH_TOKEN",
           "-e", "HTTPS_PROXY=http://ttj-native-egress:8080", "-e", "https_proxy=http://ttj-native-egress:8080",
           "-e", "DISABLE_AUTOUPDATER=1", "-e", "CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC=1",
           "ttj-native-lean422:11-11-2026-v2", "claude", "-p", "Reply with exactly: OK", "--model", "claude-fable-5-1",
           "--max-turns", "1", "--output-format", "json"]
    environment = dict(os.environ, CLAUDE_CODE_OAUTH_TOKEN=token_file.read_text().strip())
    try:
        out = subprocess.run(cmd, env=environment, capture_output=True, text=True, timeout=150).stdout
    except subprocess.TimeoutExpired:
        return False, "probe timed out"
    if '"is_error":false' in out:
        return True, "answering"
    try:
        return False, str(json.loads(out.strip().splitlines()[-1]).get("result", ""))[:300]
    except (ValueError, IndexError):
        return False, out[-300:] or "no output"


def receipt(root: Path, task: str) -> dict:
    path = root / task / "receipt.json"
    return json.loads(path.read_text()) if path.exists() else {}


def billing(r: dict) -> bool:
    return any(stop in json.dumps(r.get("native_result") or {}).lower() for stop in BILLING_STOPS)


def task_folders() -> dict[str, str]:
    """task_id -> packet task folder, for the 6 Claude cells of the 100-file cohort of record."""
    cohort = json.loads(nc.PARENT.read_text())
    layout = {**cohort["display_layout"], **cohort["layout_additions"]}
    return {a["task_id"]: layout[a["item_id"]]["task_folder"] for a in cohort["artifacts"]
            if a["configuration_id"] == nc.GROUPS["fable"]["old"]}


FOLDERS = task_folders()


def usable_in(root: Path, task: str) -> bool:
    """Exactly the cohort builder's test: bound to this condition, frozen model only, no billing stop, content screens."""
    try:
        data, _, _ = nc.cell_receipt(root, task, CONDITION, MODEL)
        nc.check_file(FOLDERS[task], data)
        return True
    except (AssertionError, FileNotFoundError, KeyError, ValueError):
        return False


def next_root(task: str):
    """Next attempt folder, or None when the cell has a usable file or has used its 3 counted attempts."""
    counted = 0
    for root in ROOTS:
        if not (root / task).exists():
            return root if counted < 3 else None
        if usable_in(root, task):
            return None
        counted += not billing(receipt(root, task))
    return None


def run_cells(state: State) -> bool:
    running: dict[str, tuple[subprocess.Popen, Path, str, bool]] = {}
    vals_fresh = False  # True once the Vals plan has refused: the next Vals cell opens a fresh 5-hour window
    last_line, last_beat = None, 0.0
    while True:
        for task, (proc, root, plan, opener) in list(running.items()):
            if proc.poll() is None:
                continue
            del running[task]
            r = receipt(root, task)
            if not (root / task).exists():  # the runner failed before starting the cell: never retry in a hot loop
                state.data["launch_failures"] = state.data.get("launch_failures", 0) + 1
                log(f"{task}: runner exited {proc.returncode} without a cell folder; see {root.name}_{task}.log")
                if state.data["launch_failures"] >= 3:
                    log("3 runner launches failed; starting no more cells")
                    state.data["deadline_unix"] = 0
                state.save()
                continue
            (root / task / "BILLING_ROUTE.json").write_text(json.dumps(
                {"route": plan, "recorded_unix": int(time.time()), "opened_fresh_vals_window": opener,
                 "note": "Which of Brando's Claude plans paid for this cell; nothing else differs."}) + "\n")
            if plan == VALS and opener and billing(r):
                state.data["vals_too_small_for"].append(task)
            state.data["cells"][task] = {"last_folder": root.name, "plan": plan, "stop_reason": r.get("stop_reason"),
                                         "bytes": r.get("candidate_bytes"), "usable": usable_in(root, task),
                                         "billing_stop": billing(r)}
            state.save()
            log(f"finished {task} in {root.name} via {plan}: {r.get('status')} {r.get('stop_reason')} "
                f"bytes={r.get('candidate_bytes')} usable={usable_in(root, task)} billing_stop={billing(r)}")
        done = [t for t in TASKS if next_root(t) is None]
        pending = [t for t in TASKS if t not in running and t not in done]
        if not running and not pending:
            missing = [t for t in TASKS if not any(usable_in(root, t) for root in ROOTS if (root / t).exists())]
            for task in TASKS:
                log(f"SUMMARY {task}: " + "; ".join(f"{root.name}={receipt(root, task).get('stop_reason')}/"
                                                    f"{receipt(root, task).get('candidate_bytes')}"
                                                    for root in ROOTS if (root / task).exists()))
            if missing:
                log(f"cells without a usable file after 3 counted attempts: {missing}")
            return not missing
        if time.time() > state.data["deadline_unix"] and not running:
            log(f"deadline reached; still missing: {pending}")
            return False
        started = False
        if pending and time.time() <= state.data["deadline_unix"]:
            status = []
            for name, token_file, limit in PLANS:
                if sum(1 for *_, plan, _o in running.values() if plan == name) >= limit:
                    continue
                choices = [t for t in pending if not (name == VALS and t in state.data["vals_too_small_for"])]
                if not choices:
                    continue
                ok, why = probe(token_file)
                state.data["plans"][name] = {"answering": ok, "said": why, "checked": time.strftime("%H:%M")}
                status.append(f"{name}: {why[:110]}")
                if name == VALS and not ok and any(s in why.lower() for s in BILLING_STOPS):
                    vals_fresh = True
                if ok:
                    task, root = choices[0], next_root(choices[0])
                    root.mkdir(parents=True, exist_ok=True)
                    out = open(N / f"{root.name}_{task}.log", "w")
                    proc = subprocess.Popen([sys.executable, str(RUNNER), "run", "--manifest", str(MANIFEST),
                                             "--condition", str(CONDITION), "--condition-sha256", CONDITION_SHA256,
                                             "--task-id", task, "--output-dir", str(root), "--token-file", str(token_file)],
                                            stdout=out, stderr=subprocess.STDOUT)
                    opener = name == VALS and vals_fresh
                    if name == VALS:
                        vals_fresh = False
                    running[task] = (proc, root, name, opener)
                    state.data["cells"][task] = {"running_in": root.name, "plan": name, "since": time.strftime("%H:%M")}
                    state.save()
                    log(f"started {task} in {root.name} via {name} ({len(running)} running)")
                    started = True
                    break
            line = " | ".join(status)
            if not started and status and (line != last_line or time.time() - last_beat > 3600):
                resets = re.findall(r"resets ([0-9:]+[ap]m \(UTC\))", line)
                log("no plan available" + (f" (Vals resets {resets[0]})" if resets else "") + ": " + line)
                last_line, last_beat = line, time.time()
                state.save()
        time.sleep(15 if started else 60)


def step(state: State, name: str, args: list, check: bool = True) -> str:
    log(f"step {name}")
    out = subprocess.run([sys.executable, *map(str, args)], cwd=REPO, capture_output=True, text=True, timeout=3600)
    state.data["steps"].append({"step": name, "exit": out.returncode, "at": time.strftime("%m-%d %H:%M:%S"),
                                "stdout_tail": out.stdout[-2000:], "stderr_tail": out.stderr[-2000:]})
    state.save()
    log(f"step {name} exit {out.returncode}: {out.stdout.strip()[-600:]} {out.stderr.strip()[-600:]}")
    if check and out.returncode != 0:
        raise RuntimeError(f"step {name} failed")
    return out.stdout


def finish(state: State) -> None:
    state.data["phase"] = "finish"
    state.save()
    step(state, "cohort", [COHORT_BUILDER, "--fable", ROOTS[0], CONDITION,
                           "--grok", N / "grok_cli_v3", N / "GROK_CLI_CONDITION_V3.json",
                           "--gemini", N / "antigravity_cli_v1", N / "ANTIGRAVITY_CONDITION_V1.json"])
    counts = {k: v for k, v in json.loads(COHORT.read_text())["actual_counts_by_configuration"].items() if v}
    assert counts == WANTED_COUNTS, f"unexpected agent counts {counts}"
    cohort_sha = hashlib.sha256(COHORT.read_bytes()).hexdigest()
    a1 = BUILDS / "A1/ASSEMBLY_RECEIPT.json"
    if a1.exists() and json.loads(a1.read_text())["cohort_sha256"] != cohort_sha:
        # The build with the 6 Terminus 2 Claude files was never sent (Brando: "I only want the CC native ones").
        index = json.loads(BUILD_INDEX.read_text())
        assert not any(e.get("sent_to_self") for e in index.values()), "an earlier native build was already sent"
        sent = SEALED / "SENT_100.json"
        assert not sent.exists() or not json.loads(sent.read_text()), "team emails were already sent"
        stamp = time.strftime("%Y%m%d-%H%M%S")
        BUILDS.rename(SEALED / f"builds_100_native_with_terminus2_claude_never_sent_{stamp}")
        BUILD_INDEX.rename(SEALED / f"BUILD_INDEX_100_NATIVE_with_terminus2_claude_never_sent_{stamp}.json")
        log(f"moved the never-sent build aside ({stamp})")
    step(state, "build", [PACKETS, "build"])
    assert json.loads(a1.read_text())["cohort_sha256"] == cohort_sha, "A1 was not built from the all-native cohort"
    step(state, "sheets", [PACKETS, "sheets"])
    index = json.loads(BUILD_INDEX.read_text())
    assert len(index) == 32 and all(e.get("rows_inserted") == 0 for e in index.values()), "Sheet rows changed"
    assert all(e["status"] == "BUILT_SHEET_MATCHED_NOT_SENT" for r, e in index.items() if r != "A1"), "a team Sheet differs"
    step(state, "drafts", [PACKETS, "drafts"])
    step(state, "review", [PACKETS, "review"])
    scored = index["A1"].get("responses_at_check", 0)
    note = ("This replaces the 100-file packet I emailed you earlier on 11-16-2026: every file now comes from its "
            "agent's own harness. Your Sheet, its rows and the file names are unchanged. "
            + ("You have not entered any scores yet, so just use this zip." if not scored else
               f"Some files' contents changed, so please re-check the {scored} rows you already filled in against "
               "the files in this zip."))
    step(state, "send-a1", [PACKETS, "send-a1", note])
    state.data["phase"] = "brando_packet_sent"
    state.save()
    approval = json.loads(TEAM_SEND_APPROVAL.read_text()) if TEAM_SEND_APPROVAL.exists() else {}
    if approval.get("quote") and approval.get("approved_by") == "Brando":
        step(state, "send-team", [PACKETS, "send", "--confirm", "--all"])
        state.data["phase"] = "all_sent"
    for name in ("export", "status"):  # record keeping; the packet is already delivered
        step(state, name, [PACKETS, name], check=False)
    state.save()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--state", type=Path, required=True)
    parser.add_argument("--hours", type=float, default=48.0, help="stop starting new cells after this many hours")
    args = parser.parse_args()
    state = State(args.state, args.hours)
    state.save()
    log(f"scheduler started; plans in order: {[p[0] for p in PLANS]}; deadline in {args.hours} h")
    if not run_cells(state):
        state.data["phase"] = "cells_missing"
        state.save()
        sys.exit(3)
    try:
        finish(state)
    except (AssertionError, RuntimeError, subprocess.TimeoutExpired, OSError, KeyError, ValueError) as error:
        state.data["phase"] = f"failed: {error!r}"[:500]
        state.save()
        log(f"FAILED: {error!r}")
        sys.exit(2)
    log("done: " + state.data["phase"])


if __name__ == "__main__":
    main()
