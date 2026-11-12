"""Reconcile private native-run receipts without generating or rewriting artifacts.

Each invocation refreshes RECONCILIATION.json. A complete, verified inventory
freezes FINAL_COHORT.json once; --ratable-subset additionally permits a separately
identified subset after every prospective attempt is terminal. Missing artifacts
remain in the complete report and EXCLUSIONS.json; they never become empty files.
"""
from __future__ import annotations

import argparse
from collections import Counter
import copy
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import time


SPEC = importlib.util.spec_from_file_location("packet_builder", Path(__file__).with_name("build_packet.py"))
BUILDER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BUILDER)
CC, PI = "native_claude_fable", "pi_gemini_flash"
PENDING = {CC: {"PREPARING", "RUNNING"}, PI: {"preparing", "running"}}
TERMINAL = {CC: {"TERMINAL", "INFRASTRUCTURE_INTERRUPTED"},
            PI: {"process_completed", "process_failed", "timeout", "runner_error",
                 "provider_error", "no_assistant_response"}}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def regular_bytes(path):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), f"Missing/nonregular file: {path}")
    return path.read_bytes()


def verified(record):
    data = regular_bytes(record["path"])
    require(sha(data) == record["sha256"], f"Hash mismatch: {record['path']}")
    return data


def json_record(record):
    return json.loads(verified(record))


def atomic_json(path, data):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(data, indent=2) + "\n")
    temporary.replace(path)


def freeze_json(path, data):
    """Do not replace an already frozen deliverable, including on a second scan."""
    encoded = (json.dumps(data, indent=2) + "\n").encode()
    if path.exists():
        require(path.read_bytes() == encoded, f"Refusing to overwrite frozen file: {path}")
    else:
        with path.open("xb") as handle:
            handle.write(encoded)
    return {"path": str(path), "sha256": sha(encoded)}


def condition_for(conditions, config, task_id):
    return conditions[config].get("_variants_by_task", {}).get(task_id, conditions[config])


def anchors(cohort, pi_index, cc_runner, pi_runner, lineage=None):
    amendment = cohort["amendment"]
    json_record(amendment["parent_manifest"])
    json_record(amendment["unchanged_assignments"])
    audit = json_record(amendment["environment_audit"])
    require(audit["status"] == "PASS" and audit["checks"] and all(audit["checks"].values()),
            "Environment audit did not pass")
    manifest = json_record(cohort["input_manifest"])
    tasks = {t["task_id"]: t for t in manifest["tasks"]}
    require(len(tasks) == len(manifest["tasks"]) == cohort["expected_tasks"], "Task inventory mismatch")
    conditions = {}
    for config, runner in ((CC, cc_runner), (PI, pi_runner)):
        record = cohort["configurations"][config]
        condition = json_record(record["planned_condition_snapshot"])
        require(condition["status"] == "FROZEN", "Condition is not frozen")
        require(condition["model"] == record["model"] and condition["effort"] == record["effort"],
                "Configured model/effort mismatch")
        require(condition["input_manifest_sha256"] == cohort["input_manifest"]["sha256"],
                "Condition/input manifest mismatch")
        require(condition["docker_image"] == audit["image_id"], "Condition/image audit mismatch")
        if lineage is None:
            require(sha(regular_bytes(runner)) == condition["runner_sha256"], "Frozen runner hash mismatch")
        conditions[config] = condition
    if lineage is not None:
        require(set(lineage["configurations"]) == {CC, PI}, "Condition lineage must cover both native configurations")
        for config, variants in lineage["configurations"].items():
            base = conditions[config]
            bound = {}
            for variant in variants:
                condition = json_record(variant["condition"])
                require(sha(verified(variant["runner"])) == condition["runner_sha256"], "Archived runner mismatch")
                # Operational amendments are hash-bound. Scientific inputs and
                # original budgets cannot change under the same cell IDs.
                require(all(condition.get(k) == v for k, v in base.items()
                            if k not in {"runner_sha256", "frozen_at", "parent_authorization"}),
                        "Lineage changed a frozen condition")
                require(Path(variant["output_root"]).resolve() ==
                        Path(cohort["configurations"][config]["output_root"]).resolve(), "Lineage output root changed")
                condition["_condition_snapshot"] = variant["condition"]
                for tid in variant["task_ids"]:
                    require(tid in tasks and tid not in bound, "Duplicate/unknown lineage task")
                    bound[tid] = condition
            require(set(bound) == set(tasks), "Condition lineage does not cover every task")
            base["_variants_by_task"] = bound
    index = json_record({"path": str(pi_index), "sha256": conditions[PI]["task_manifest_index_sha256"]})
    pi_cells = {c["task_id"]: c for c in index["cells"]}
    require(set(pi_cells) == set(tasks) and len(pi_cells) == len(index["cells"]), "Pi task index mismatch")
    return tasks, conditions, pi_cells


def missing_cause(config, receipt, receipt_path, condition):
    """Separate procedure limits from infrastructure, preserving exact evidence."""
    if config == CC:
        evidence = {k: receipt.get(k) for k in ("status", "stop_reason", "model_call_performed", "error_type")}
        native = receipt.get("native_result") or {}
        evidence["native_result_subtype"] = native.get("subtype")
        if receipt["status"] == "INFRASTRUCTURE_INTERRUPTED" or receipt.get("model_call_performed") is not True:
            cause = "infrastructure:" + ("before_model_call" if receipt.get("model_call_performed") is not True else "runner_interrupted")
        elif receipt.get("stop_reason") == "wall_time_budget":
            cause = "timeout"
        elif receipt.get("stop_reason") in {"observed_total_token_budget", "observed_output_token_budget"}:
            cause = "budget_cap:" + receipt["stop_reason"]
        elif native.get("subtype") in {"error_max_turns", "error_max_budget_usd"}:
            cause = "budget_cap:" + native["subtype"]
        elif native.get("is_error") or receipt.get("stop_reason") == "process_exit_without_result":
            cause = "infrastructure:native_error_or_incomplete_result"
        else:
            cause = "ended_without_file"
        return cause, evidence
    ledger_path = receipt_path.with_name("gateway_ledger.json")
    if not ledger_path.exists():
        return "infrastructure:missing_gateway_ledger", {"ledger_path": str(ledger_path),
            "cost_upper_bound_usd": condition["max_cost_per_cell_usd"], "observed_cost_unavailable": True}
    raw = regular_bytes(ledger_path)
    ledger = json.loads(raw)
    require(ledger.get("model") == condition["model"] and ledger.get("cap_usd") == condition["max_cost_per_cell_usd"],
            "Gateway ledger condition mismatch")
    denials, requests = ledger.get("denials", []), ledger.get("requests", [])
    last_denial = denials[-1] if denials else {}
    last_request = requests[-1] if requests else {}
    reason = str(last_denial.get("reason", ""))
    evidence = {"gateway_ledger": {"path": str(ledger_path), "sha256": sha(raw)},
        "last_denial": last_denial, "request_count": len(requests),
        "last_request": {k: last_request.get(k) for k in ("call", "http_status", "provider_finish_reason", "admitted_at", "finished_at")},
        "accounted_usd": ledger.get("accounted_usd"), "execution_status": receipt["status"]}
    if reason in {"Provider request cap reached", "Cell dollar cap cannot admit next request", "Dollar cap reached",
                  "Input token cap exceeded", "Output token cap exceeded"}:
        failed_requests = [r for r in requests if r.get("http_status") != 200 or r.get("provider_finish_reason") is None]
        evidence["contributing_incomplete_or_error_requests"] = len(failed_requests)
        cause = "infrastructure:budget_cap_after_provider_errors" if failed_requests else "budget_cap:" + reason
    elif receipt["status"] == "timeout":
        cause = "timeout"
    elif receipt["status"] == "runner_error" or reason or (last_request and
            (last_request.get("http_status") != 200 or last_request.get("provider_finish_reason") is None)):
        cause = "infrastructure:" + (reason or receipt["status"])
    elif receipt["status"] in {"provider_error", "no_assistant_response", "process_failed"}:
        cause = "infrastructure:" + receipt["status"]
    else:
        cause = "ended_without_file"
    return cause, evidence


def validate_receipt(artifact, receipt, cohort, tasks, conditions, pi_cells):
    config, tid = artifact["configuration_id"], artifact["task_id"]
    condition, task = condition_for(conditions, config, tid), tasks[tid]
    require(receipt["task_id"] == tid, "Receipt task ID mismatch")
    require(artifact["provenance"]["instruction_sha256"] == task["files"]["instruction.md"],
            "Instruction provenance mismatch")
    if config == CC:
        snapshot = condition.get("_condition_snapshot", cohort["configurations"][config]["planned_condition_snapshot"])
        require(receipt["condition_sha256"] == snapshot["sha256"], "Receipt condition mismatch")
        require(receipt["visible_files"] == task["files"], "Receipt source files mismatch")
        require(receipt["output"] == task["expected_solver_output_path"], "Requested output path mismatch")
        command = receipt["command"]
        for flag, value in (("--model", condition["model"]), ("--effort", condition["effort"]),
                            ("--max-turns", str(condition["max_turns"]))):
            require(command.count(flag) == 1 and command[command.index(flag) + 1] == value,
                    f"Receipt command differs at {flag}")
        if receipt["status"] not in {"PREPARING", "INFRASTRUCTURE_INTERRUPTED"}:
            require(receipt.get("actual_mounts") == [], "Unexpected/unverified host mounts")
            require(receipt.get("network") == "ttj-native-source-only", "Unexpected runner network")
            require("SOURCE_ONLY_USER1001_MATHLIB_PREFLIGHT_OK" in receipt.get("runtime_preflight", ""),
                    "Missing source-only nonroot preflight")
            require(receipt.get("cli_version", "").split()[0] == condition["cli_version"],
                    "Claude Code version mismatch")
    else:
        cell = pi_cells[tid]
        require(Path(cell["output_dir"]).resolve() == Path(artifact["candidate"]["path"]).parent.resolve(),
                "Pi index output root mismatch")
        cell_manifest = json_record({"path": cell["manifest"], "sha256": cell["manifest_sha256"]})
        require(cell_manifest["task_id"] == tid and cell_manifest["source_only_approval"] is True,
                "Pi task manifest identity/approval mismatch")
        require(cell_manifest["files"] == task["files"] == receipt["input_files"], "Pi source files mismatch")
        require(cell_manifest["parent_input_manifest_sha256"] == cohort["input_manifest"]["sha256"],
                "Pi parent input manifest mismatch")
        require(cell_manifest["output_file"] == task["output_file"], "Pi requested output mismatch")
        require(receipt["manifest_sha256"] == cell["manifest_sha256"], "Pi receipt manifest mismatch")
        pairs = {"model": "model", "thinking": "effort", "image_id": "docker_image",
                 "runner_sha256": "runner_sha256", "cell_cap_usd": "max_cost_per_cell_usd",
                 "request_cap": "max_provider_requests_per_cell", "wall_seconds": "max_seconds_per_cell",
                 "input_token_cap": "max_input_tokens_per_request", "output_token_cap": "max_output_tokens_per_request"}
        require(all(receipt.get(r) == condition[c] for r, c in pairs.items()), "Pi execution condition mismatch")
        require(receipt.get("host_mounts") == [] and receipt.get("attempts") == 1, "Pi mounts/attempts mismatch")
        if receipt["status"] not in {"preparing", "runner_error"}:
            require(receipt.get("runtime_uid") == 1001, "Pi runtime UID mismatch")
            require(receipt.get("pi_version_observed") == condition["cli_version"], "Pi CLI version mismatch")


def resolve_artifact(artifact, cohort, tasks, conditions, pi_cells):
    row = {"item_id": artifact["item_id"], "task_id": artifact["task_id"],
           "configuration_id": artifact["configuration_id"], "terminal": False,
           "state": "INVALID_PROVENANCE", "candidate_path": artifact["candidate"]["path"]}
    try:
        tid, config = artifact["task_id"], artifact["configuration_id"]
        task = tasks[tid]
        for kind in ("python", "gold"):
            require(bool(verified(artifact[kind])), f"Empty {kind}")
        python_path = Path(artifact["python"]["path"])
        require(task["files"].get(python_path.name) == artifact["python"]["sha256"], "Python/input manifest mismatch")
        for name, expected in task["files"].items():
            verified({"path": str(Path(task["source_dir"]) / name), "sha256": expected})
        candidate = Path(artifact["candidate"]["path"])
        excluded = cohort["amendment"]["invalid_pilot_disposition"]["excluded_output_roots"]
        require(not any(candidate.resolve().is_relative_to(Path(p).resolve()) for p in excluded),
                "Invalid pilot output root is excluded")
        if config not in (CC, PI):
            data = verified(artifact["candidate"])
            require(artifact["candidate"]["status"] == ("empty" if not data else "nonempty"),
                    "Historical candidate status mismatch")
            row.update(state="HISTORICAL_VERIFIED", terminal=True, candidate_sha256=sha(data), candidate_bytes=len(data))
            return row
        root = Path(cohort["configurations"][config]["output_root"]).resolve()
        expected_path = root / tid / "candidate.lean"
        receipt_path = Path(artifact["provenance"]["expected_receipt_path"])
        require(candidate.absolute() == expected_path and candidate.resolve() == expected_path,
                "Candidate path/symlink escapes the frozen valid root")
        require(receipt_path.absolute() == root / tid / "receipt.json" and receipt_path.resolve() == receipt_path.absolute(),
                "Receipt path/symlink escapes the frozen valid root")
        row["receipt_path"] = str(receipt_path)
        if not receipt_path.exists():
            row.update(state="PENDING", reason="No receipt yet; not a failed attempt")
            return row
        raw = regular_bytes(receipt_path)
        try:
            receipt = json.loads(raw)
        except json.JSONDecodeError:
            row.update(state="PENDING", reason="Receipt unreadable during scan; terminal outcome unverified")
            return row
        row.update(receipt_sha256=sha(raw), execution_status=receipt.get("status"),
                   terminal=receipt.get("status") in TERMINAL[config])
        validate_receipt(artifact, receipt, cohort, tasks, conditions, pi_cells)
        condition = condition_for(conditions, config, tid)
        row["execution_condition"] = condition.get("_condition_snapshot",
            cohort["configurations"][config]["planned_condition_snapshot"])
        row["runner_sha256"] = condition["runner_sha256"]
        if receipt["status"] in PENDING[config]:
            row.update(state="PENDING", reason="Attempt still in progress")
            return row
        require(row["terminal"], "Unknown receipt execution status")
        require(receipt.get("finished_at") is not None, "Terminal receipt has no completion timestamp")
        captured = receipt.get("candidate_captured") if config == CC else receipt.get("artifact_status") in {"present", "empty"}
        row.update(stop_reason=receipt.get("stop_reason", receipt.get("native_stop_reason")), exit_code=receipt.get("exit_code"))
        if not captured:
            require(not candidate.exists(), "Receipt says missing but a candidate file exists")
            cause, evidence = missing_cause(config, receipt, receipt_path, condition)
            row.update(state="MISSING_OUTPUT", reason="Terminal attempt returned no captured artifact",
                       missing_cause=cause, missing_cause_evidence=evidence,
                       solver_failure_attributable=not cause.startswith("infrastructure:"))
            return row
        data = regular_bytes(candidate)
        expected_hash = receipt.get("candidate_sha256" if config == CC else "artifact_sha256")
        expected_size = receipt.get("candidate_bytes" if config == CC else "artifact_bytes")
        require(sha(data) == expected_hash and len(data) == expected_size, "Candidate receipt hash/size mismatch")
        if config == CC:
            models = receipt.get("actual_models", [])
            require(receipt.get("model_identity_verified") is True and models and all(
                m == condition_for(conditions, config, tid)["model"]
                or m.startswith(condition_for(conditions, config, tid)["model"] + "-") for m in models),
                "Actual Claude model identity is unverified")
        else:
            require(receipt.get("actual_model") == condition_for(conditions, config, tid)["model"]
                    and receipt.get("actual_thinking") == condition_for(conditions, config, tid)["effort"]
                    and receipt.get("actual_provider") == "allen-google-veribench", "Actual Pi identity is unverified")
            require(receipt["artifact_status"] == ("empty" if not data.strip() else "present"),
                    "Pi artifact classification contradicts bytes")
        row.update(state="RATABLE", candidate_sha256=sha(data), candidate_bytes=len(data),
                   candidate_status="empty" if not data else "nonempty",
                   blank_content=not bool(data.strip()), actual_model_verified=True)
        # A returned file may be a partial answer after a timeout/error. Preserve
        # that execution status; byte availability is not semantic correctness.
    except (ValueError, KeyError, IndexError, TypeError, OSError) as exc:
        row.update(state="INVALID_PROVENANCE", reason=str(exc))
    return row


def reconcile(cohort_path, expected_sha256, *, pi_index, cc_runner, pi_runner, lineage_record=None):
    cohort_path = Path(cohort_path).resolve()
    cohort = json_record({"path": str(cohort_path), "sha256": expected_sha256})
    lineage = json_record(lineage_record) if lineage_record else None
    if lineage:
        require(lineage["planned_cohort"] == {"path": str(cohort_path), "sha256": expected_sha256},
                "Condition lineage refers to a different planned cohort")
    tasks, conditions, pi_cells = anchors(cohort, pi_index, cc_runner, pi_runner, lineage)
    artifacts = cohort["artifacts"]
    require(len(artifacts) == cohort["expected_artifacts"], "Planned artifact count mismatch")
    require(len({a["item_id"] for a in artifacts}) == len(artifacts), "Duplicate item IDs")
    require(len({(a["task_id"], a["configuration_id"]) for a in artifacts}) == len(artifacts), "Duplicate cells")
    rows = [resolve_artifact(a, cohort, tasks, conditions, pi_cells) for a in artifacts]
    disposition_record = lineage.get("infrastructure_disposition") if lineage else None
    disposition = json_record(disposition_record) if disposition_record else None
    authorized = {}
    if disposition:
        require(disposition["planned_cohort"] == {"path": str(cohort_path), "sha256": expected_sha256},
                "Infrastructure disposition uses a different cohort")
        authorized = {row["item_id"]: row for row in disposition["excluded_cells"]}
        require(len(authorized) == len(disposition["excluded_cells"]), "Duplicate infrastructure disposition")
    unapproved = []
    for row in rows:
        if row.get("missing_cause", "").startswith("infrastructure:"):
            entry = authorized.get(row["item_id"], {})
            row["infrastructure_exclusion_authorized"] = (
                entry.get("task_id") == row["task_id"] and entry.get("configuration_id") == row["configuration_id"]
                and entry.get("receipt_sha256") == row["receipt_sha256"]
                and entry.get("missing_cause") == row["missing_cause"]
                and entry.get("gateway_ledger") == row["missing_cause_evidence"].get("gateway_ledger")
                and entry.get("disposition") == "EXCLUDE_INFRASTRUCTURE_NOT_SOLVER_FAILURE")
            if not row["infrastructure_exclusion_authorized"]:
                unapproved.append(row["item_id"])
    counts = dict(Counter(row["state"] for row in rows))
    prospective = [row for row in rows if row["configuration_id"] in (CC, PI)]
    terminal = all(row["terminal"] for row in prospective)
    ready = all(row["state"] in {"RATABLE", "HISTORICAL_VERIFIED"} for row in rows)
    report = {"schema_version": 1, "checked_at": datetime.now(timezone.utc).isoformat(),
              "planned_cohort": {"path": str(cohort_path), "sha256": expected_sha256},
              "planned_artifacts": len(rows), "prospective_attempts": len(prospective),
              "terminal_prospective_attempts": sum(row["terminal"] for row in prospective),
              "all_prospective_terminal": terminal, "full_cohort_buildable": ready,
              "ratable_subset_available": terminal and not counts.get("INVALID_PROVENANCE", 0) and not unapproved,
              "counts": counts, "cells": rows,
              "condition_lineage": lineage_record,
              "infrastructure_disposition": disposition_record,
              "infrastructure_items_awaiting_disposition": unapproved,
              "scope": "Artifact availability/provenance only; no ratings, scores, inference or candidate changes.",
              "cc_image_evidence": "Immutable condition plus hash-verified runner and per-cell runtime preflight; CC receipts do not independently record an actual image digest."}
    return cohort, report


def save_reconciliation(cohort, report, output_dir, *, ratable_subset=False):
    output_dir = Path(output_dir).resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    atomic_json(output_dir / "RECONCILIATION.json", report)
    ready = report["full_cohort_buildable"]
    if not ready and not (ratable_subset and report["ratable_subset_available"]):
        return None
    rows = {r["item_id"]: r for r in report["cells"]}
    accepted = {item for item, row in rows.items() if row["state"] in {"RATABLE", "HISTORICAL_VERIFIED"}}
    require(bool(accepted), "No real files are available for a ratable cohort")
    # Finalization is a new read barrier after reconciliation, so an updated
    # receipt/file cannot be silently frozen from a stale monitoring snapshot.
    json_record(report["planned_cohort"])
    if report["condition_lineage"]:
        json_record(report["condition_lineage"])
    if report["infrastructure_disposition"]:
        json_record(report["infrastructure_disposition"])
    for artifact in cohort["artifacts"]:
        row = rows[artifact["item_id"]]
        if "receipt_sha256" in row:
            verified({"path": row["receipt_path"], "sha256": row["receipt_sha256"]})
        ledger = row.get("missing_cause_evidence", {}).get("gateway_ledger")
        if ledger:
            verified(ledger)
        if artifact["item_id"] in accepted:
            for kind in ("python", "gold"):
                verified(artifact[kind])
            verified({"path": row["candidate_path"], "sha256": row["candidate_sha256"]})
        else:
            require(not Path(row["candidate_path"]).exists(), "Missing output appeared after reconciliation")
    final = copy.deepcopy(cohort)
    final.update(status="FINAL_FULL_COHORT" if ready else "FINAL_RATABLE_SUBSET", buildable=True,
                 planned_cohort=report["planned_cohort"], planned_artifacts=report["planned_artifacts"],
                 display_layout=BUILDER.display_layout(cohort["artifacts"], cohort["shuffle_seed"]),
                 excluded_item_ids=[a["item_id"] for a in cohort["artifacts"] if a["item_id"] not in accepted])
    if report["condition_lineage"]:
        final["condition_lineage"] = report["condition_lineage"]
    if report["infrastructure_disposition"]:
        final["infrastructure_disposition"] = report["infrastructure_disposition"]
    final["artifacts"] = [a for a in final["artifacts"] if a["item_id"] in accepted]
    final["expected_artifacts"] = len(final["artifacts"])
    final["expected_tasks"] = len({a["task_id"] for a in final["artifacts"]})
    final["actual_counts_by_configuration"] = dict(Counter(a["configuration_id"] for a in final["artifacts"]))
    if "finalization_requirements" in final:
        final["original_planning_requirements"] = final.pop("finalization_requirements")
    final["counts"] = {"planned_artifacts": report["planned_artifacts"], "ratable_artifacts": len(accepted),
                       "excluded_missing_outputs": len(rows) - len(accepted), "prospective_candidates_pending": 0}
    for artifact in final["artifacts"]:
        row = rows[artifact["item_id"]]
        if artifact["configuration_id"] in (CC, PI):
            artifact["candidate"].update(status=row["candidate_status"], sha256=row["candidate_sha256"])
            artifact["provenance"].update(receipt_sha256=row["receipt_sha256"], execution_verified=True,
                                          execution_status=row["execution_status"], stop_reason=row["stop_reason"],
                                          execution_condition=row["execution_condition"], runner_sha256=row["runner_sha256"],
                                          candidate_bytes=row["candidate_bytes"], blank_content=row["blank_content"],
                                          note="Actual returned bytes, including partial/empty artifacts; execution status is preserved and is not a correctness verdict.")
    exclusions = {"planned_cohort": report["planned_cohort"], "planned_artifacts": len(rows),
                  "ratable_artifacts": len(accepted), "all_prospective_terminal": True,
                  "excluded_cells": [r for r in report["cells"] if r["item_id"] not in accepted],
                  "rule": "Missing outputs remain in the complete execution denominator; no substitute, retry, generated empty file or imputed score."}
    # Exclude volatile scan timestamps: repeat scans are deterministic and cannot
    # silently replace a freeze after a source receipt or candidate changes.
    exclusions_record = freeze_json(output_dir / "EXCLUSIONS.json", exclusions)
    final["exclusions"] = exclusions_record
    name = "FINAL_COHORT.json" if ready else "RATABLE_COHORT.json"
    return freeze_json(output_dir / name, final)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cohort", type=Path, required=True)
    parser.add_argument("--cohort-sha256", required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--pi-index", type=Path, required=True)
    parser.add_argument("--cc-runner", type=Path, default=Path(__file__).with_name("claude_code_runner.py"))
    parser.add_argument("--pi-runner", type=Path, default=Path(__file__).with_name("pi_runner.py"))
    parser.add_argument("--condition-lineage", type=Path)
    parser.add_argument("--condition-lineage-sha256")
    parser.add_argument("--ratable-subset", action="store_true")
    parser.add_argument("--watch", action="store_true", help="Monitor receipts until all prospective attempts are terminal")
    parser.add_argument("--poll-seconds", type=float, default=30)
    parser.add_argument("--watch-seconds", type=float, default=54000,
                        help="Bound the monitor; timeout never relabels pending attempts as failed")
    args = parser.parse_args()
    require(1 <= args.poll_seconds <= 60, "Poll interval must be 1–60 seconds")
    require(0 < args.watch_seconds <= 172800, "Watch duration must be positive and at most 48 hours")
    require(bool(args.condition_lineage) == bool(args.condition_lineage_sha256), "Lineage needs its frozen hash")
    lineage_record = ({"path": str(args.condition_lineage.resolve()), "sha256": args.condition_lineage_sha256}
                      if args.condition_lineage else None)
    previous = None
    deadline = time.monotonic() + args.watch_seconds
    while True:
        cohort, report = reconcile(args.cohort, args.cohort_sha256, pi_index=args.pi_index,
                                   cc_runner=args.cc_runner, pi_runner=args.pi_runner, lineage_record=lineage_record)
        frozen = save_reconciliation(cohort, report, args.output_dir, ratable_subset=args.ratable_subset)
        state = {"counts": report["counts"], "terminal": report["terminal_prospective_attempts"],
                 "prospective": report["prospective_attempts"], "frozen": frozen}
        if state != previous:
            print(json.dumps(state, sort_keys=True), flush=True)
            previous = state
        if frozen or not args.watch or report["all_prospective_terminal"]:
            return
        if time.monotonic() >= deadline:
            print(json.dumps({"monitor_status": "TIME_LIMIT", "pending_outcomes_unchanged": True}), flush=True)
            return
        time.sleep(args.poll_seconds)


if __name__ == "__main__":
    main()
