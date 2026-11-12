"""Synthetic provenance, missingness, freeze and stable-path regression checks."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest


EXP = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("cohort_finalizer",
    EXP / "support/scripts/native_packet_generation/finalize_cohort.py")
F = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(F)


class FinalizerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.task_id = "task_one"
        self.inputs = self.root / "source_only"
        self.inputs.mkdir()
        self.py = self.inputs / "source.py"
        self.py.write_bytes(b"def f(x): return x\n")
        self.instruction = self.inputs / "instruction.md"
        self.instruction.write_text("Write formal specification statements.\n")
        self.gold = self.root / "gold.lean"
        self.gold.write_bytes(b"theorem reference : True := by trivial\n")
        self.files = {p.name: self.sha(p) for p in (self.py, self.instruction)}
        task = {"task_id": self.task_id, "source_dir": str(self.inputs), "files": self.files,
                "output_file": "Veribench/task_one.lean",
                "expected_solver_output_path": "/home/user/lean_project/Veribench/task_one.lean"}
        self.input_manifest = self.write("INPUT.json", {"tasks": [task]})
        self.runner = self.root / "frozen_runner.py"
        self.runner.write_text("# synthetic frozen runner\n")
        image = "sha256:" + "a" * 64
        audit = self.write("AUDIT.json", {"status": "PASS", "checks": {"clean": True}, "image_id": image})
        self.cc_root, self.pi_root = self.root / "cc_valid", self.root / "pi_valid"
        for root in (self.cc_root, self.pi_root):
            (root / self.task_id).mkdir(parents=True)
        cell_manifest = self.write("PI_TASK.json", {"task_id": self.task_id, "files": self.files,
            "source_only_approval": True, "parent_input_manifest_sha256": self.sha(self.input_manifest),
            "output_file": task["output_file"]})
        self.pi_index = self.write("PI_INDEX.json", {"cells": [{"task_id": self.task_id,
            "manifest": str(cell_manifest), "manifest_sha256": self.sha(cell_manifest),
            "output_dir": str(self.pi_root / self.task_id)}]})
        common = {"status": "FROZEN", "docker_image": image, "runner_sha256": self.sha(self.runner),
                  "input_manifest_sha256": self.sha(self.input_manifest)}
        cc = self.write("CC_CONDITION.json", {**common, "model": "claude-fable-5-1", "effort": "max",
                "max_turns": 40, "cli_version": "2.1.322"})
        pi = self.write("PI_CONDITION.json", {**common, "model": "gemini-3.8-flash", "effort": "high",
            "cli_version": "1.5.2", "task_manifest_index_sha256": self.sha(self.pi_index),
            "max_cost_per_cell_usd": .75, "max_provider_requests_per_cell": 40,
            "max_seconds_per_cell": 1800, "max_input_tokens_per_request": 65536,
            "max_output_tokens_per_request": 16384})
        historical = self.root / "historical.lean"
        historical.write_bytes(b"-- exact historical candidate\r\n")
        artifacts = []
        for i, (config, path) in enumerate([
            ("historical_codex_astra", historical), (F.CC, self.cc_root / self.task_id / "candidate.lean"),
            (F.PI, self.pi_root / self.task_id / "candidate.lean")], 1):
            artifacts.append({"task_id": self.task_id, "task_description": "Identity operation",
                "item_id": f"synthetic-round__item{i:03d}", "configuration_id": config,
                "python": self.record(self.py), "gold": self.record(self.gold),
                "candidate": {"path": str(path), "sha256": self.sha(path) if i == 1 else None,
                              "status": "nonempty" if i == 1 else "pending"},
                "provenance": {"expected_receipt_path": str(path.with_name("receipt.json")),
                               "instruction_sha256": self.sha(self.instruction)}})
        parent = self.write("PARENT.json", {"original": True})
        assignments = self.write("ASSIGNMENTS.json", {"unchanged": True})
        self.cohort = {"schema_version": 1, "round_id": "synthetic-round", "shuffle_seed": "stable-seed",
            "status": "PLANNED_PENDING_GENERATION", "buildable": False,
            "expected_tasks": 1, "expected_artifacts": 3,
            "input_manifest": self.record(self.input_manifest), "artifacts": artifacts,
            "configurations": {
                "historical_codex_astra": {"model": "gpt-6-astra", "harness": "Codex"},
                F.CC: {"model": "claude-fable-5-1", "effort": "max", "output_root": str(self.cc_root),
                       "planned_condition_snapshot": self.record(cc)},
                F.PI: {"model": "gemini-3.8-flash", "effort": "high", "output_root": str(self.pi_root),
                       "planned_condition_snapshot": self.record(pi)}},
            "amendment": {"parent_manifest": self.record(parent), "unchanged_assignments": self.record(assignments),
                "environment_audit": self.record(audit),
                "invalid_pilot_disposition": {"excluded_output_roots": [str(self.root / "invalid_pilot")]}}}
        self.cohort_path = self.write("PLANNED.json", self.cohort)
        cc_path = Path(artifacts[1]["candidate"]["path"])
        cc_path.write_bytes(b"-- partial returned file\r\n")
        self.cc_receipt_path = cc_path.with_name("receipt.json")
        self.cc_receipt = {"task_id": self.task_id, "condition_sha256": self.sha(cc), "visible_files": self.files,
            "output": task["expected_solver_output_path"], "command": ["claude", "--model", "claude-fable-5-1",
            "--effort", "max", "--max-turns", "40"], "actual_mounts": [], "network": "ttj-native-source-only",
            "runtime_preflight": "SOURCE_ONLY_USER1001_MATHLIB_PREFLIGHT_OK", "cli_version": "2.1.322",
            "status": "TERMINAL", "finished_at": 1, "candidate_captured": True,
            "candidate_sha256": self.sha(cc_path), "candidate_bytes": cc_path.stat().st_size,
            "actual_models": ["claude-fable-5-1-20261101"], "model_identity_verified": True,
            "stop_reason": "wall_time_budget", "exit_code": -15}
        self.write(self.cc_receipt_path, self.cc_receipt)
        pi_path = Path(artifacts[2]["candidate"]["path"])
        pi_path.write_bytes(b"")
        self.pi_receipt_path = pi_path.with_name("receipt.json")
        self.pi_receipt = {"task_id": self.task_id, "manifest_sha256": self.sha(cell_manifest),
            "input_files": self.files, "model": "gemini-3.8-flash", "thinking": "high",
            "image_id": image, "runner_sha256": self.sha(self.runner), "cell_cap_usd": .75,
            "request_cap": 40, "wall_seconds": 1800, "input_token_cap": 65536, "output_token_cap": 16384,
            "host_mounts": [], "attempts": 1, "runtime_uid": 1001, "pi_version_observed": "1.5.2",
            "status": "timeout", "finished_at": "synthetic", "artifact_status": "empty",
            "artifact_sha256": self.sha(pi_path), "artifact_bytes": 0,
            "actual_model": "gemini-3.8-flash", "actual_thinking": "high", "actual_provider": "allen-google-veribench"}
        self.write(self.pi_receipt_path, self.pi_receipt)
        self.ledger_path = self.pi_receipt_path.with_name("gateway_ledger.json")
        self.ledger = {"model": "gemini-3.8-flash", "cap_usd": .75, "denials": [], "requests": []}
        self.write(self.ledger_path, self.ledger)

    @staticmethod
    def sha(path):
        return hashlib.sha256(path.read_bytes()).hexdigest()

    def record(self, path):
        return {"path": str(path), "sha256": self.sha(path)}

    def write(self, name, obj):
        path = self.root / name
        path.write_text(json.dumps(obj))
        return path

    def scan(self):
        return F.reconcile(self.cohort_path, self.sha(self.cohort_path), pi_index=self.pi_index,
                           cc_runner=self.runner, pi_runner=self.runner)

    def test_freeze_preserves_real_bytes_failure_status_and_explicit_empty(self):
        before = {a["candidate"]["path"]: Path(a["candidate"]["path"]).read_bytes() for a in self.cohort["artifacts"]}
        cohort, report = self.scan()
        self.assertTrue(report["full_cohort_buildable"])
        out = self.root / "finalization"
        frozen = F.save_reconciliation(cohort, report, out)
        final = json.loads(Path(frozen["path"]).read_text())
        self.assertEqual(final["expected_artifacts"], 3)
        self.assertEqual(final["artifacts"][1]["provenance"]["stop_reason"], "wall_time_budget")
        self.assertEqual(final["artifacts"][2]["candidate"]["status"], "empty")
        self.assertEqual(F.save_reconciliation(*self.scan(), out), frozen)
        self.assertEqual(before, {p: Path(p).read_bytes() for p in before})

    def test_pending_is_not_failure_and_missing_does_not_become_empty(self):
        Path(self.cohort["artifacts"][2]["candidate"]["path"]).unlink()
        self.pi_receipt.update(status="running")
        self.write(self.pi_receipt_path, self.pi_receipt)
        cohort, report = self.scan()
        self.assertEqual(report["cells"][2]["state"], "PENDING")
        self.assertFalse(report["all_prospective_terminal"])
        self.assertIsNone(F.save_reconciliation(cohort, report, self.root / "out", ratable_subset=True))
        self.pi_receipt.update(status="process_completed", artifact_status="missing")
        self.write(self.pi_receipt_path, self.pi_receipt)
        cohort, report = self.scan()
        self.assertEqual(report["cells"][2]["state"], "MISSING_OUTPUT")
        self.assertTrue(report["all_prospective_terminal"])
        self.assertIsNone(F.save_reconciliation(cohort, report, self.root / "out"))
        frozen = F.save_reconciliation(cohort, report, self.root / "out", ratable_subset=True)
        final = json.loads(Path(frozen["path"]).read_text())
        self.assertEqual((final["planned_artifacts"], final["expected_artifacts"]), (3, 2))
        self.assertEqual(final["excluded_item_ids"], [self.cohort["artifacts"][2]["item_id"]])
        self.assertEqual(final["display_layout"], F.BUILDER.display_layout(self.cohort["artifacts"], "stable-seed"))
        self.assertFalse(Path(self.cohort["artifacts"][2]["candidate"]["path"]).exists())

    def test_wrong_task_condition_image_and_hash_are_rejected(self):
        mutations = [(self.cc_receipt_path, self.cc_receipt, "task_id", "another_task"),
                     (self.cc_receipt_path, self.cc_receipt, "condition_sha256", "0" * 64),
                     (self.pi_receipt_path, self.pi_receipt, "image_id", "sha256:" + "b" * 64),
                     (self.pi_receipt_path, self.pi_receipt, "artifact_sha256", "0" * 64)]
        for path, original, key, bad in mutations:
            with self.subTest(key=key):
                self.write(path, {**original, key: bad})
                _, report = self.scan()
                self.assertEqual(report["counts"].get("INVALID_PROVENANCE"), 1)
                self.assertFalse(report["ratable_subset_available"])
                self.write(path, original)

    def test_invalid_root_and_symlink_cannot_enter_cohort(self):
        invalid = self.root / "invalid_pilot" / self.task_id
        invalid.mkdir(parents=True)
        (invalid / "candidate.lean").write_bytes(b"old pilot")
        self.cohort["artifacts"][1]["candidate"]["path"] = str(invalid / "candidate.lean")
        self.write(self.cohort_path, self.cohort)
        _, report = self.scan()
        self.assertEqual(report["cells"][1]["state"], "INVALID_PROVENANCE")
        self.assertIn("Invalid pilot", report["cells"][1]["reason"])

    def test_absent_receipt_is_pending_and_changed_source_is_invalid(self):
        self.cc_receipt_path.unlink()
        _, report = self.scan()
        self.assertEqual(report["cells"][1]["state"], "PENDING")
        self.py.write_bytes(b"changed source")
        _, report = self.scan()
        self.assertEqual(report["counts"]["INVALID_PROVENANCE"], 3)

    def test_frozen_file_is_not_overwritten(self):
        cohort, report = self.scan()
        out = self.root / "out"
        frozen = F.save_reconciliation(cohort, report, out)
        original = Path(frozen["path"]).read_bytes()
        self.cc_receipt["stop_reason"] = "native_result"
        self.write(self.cc_receipt_path, self.cc_receipt)
        with self.assertRaisesRegex(ValueError, "Refusing to overwrite"):
            F.save_reconciliation(*self.scan(), out)
        self.assertEqual(Path(frozen["path"]).read_bytes(), original)

    def test_diagnostics_lineage_binds_exact_runner_and_rejects_budget_change(self):
        runner_v4 = self.root / "runner_v4.py"
        runner_v4.write_text("# diagnostics-only synthetic runner\n")
        condition = json.loads((self.root / "PI_CONDITION.json").read_text())
        condition["runner_sha256"] = self.sha(runner_v4)
        revised = self.write("PI_V4.json", condition)
        lineage = {"planned_cohort": self.record(self.cohort_path), "configurations": {
            F.CC: [{"condition": self.record(self.root / "CC_CONDITION.json"), "runner": self.record(self.runner),
                    "output_root": str(self.cc_root), "task_ids": [self.task_id]}],
            F.PI: [{"condition": self.record(revised), "runner": self.record(runner_v4),
                    "output_root": str(self.pi_root), "task_ids": [self.task_id]}]}}
        lp = self.write("LINEAGE.json", lineage)
        def scan():
            return F.reconcile(self.cohort_path, self.sha(self.cohort_path), pi_index=self.pi_index,
                               cc_runner=self.runner, pi_runner=self.runner, lineage_record=self.record(lp))
        _, report = scan()
        self.assertEqual(report["cells"][2]["state"], "INVALID_PROVENANCE")
        self.pi_receipt["runner_sha256"] = self.sha(runner_v4)
        self.write(self.pi_receipt_path, self.pi_receipt)
        _, report = scan()
        self.assertTrue(report["full_cohort_buildable"])
        self.assertEqual(report["cells"][2]["execution_condition"], self.record(revised))
        condition["max_cost_per_cell_usd"] = 10
        self.write(revised, condition)
        lineage["configurations"][F.PI][0]["condition"] = self.record(revised)
        self.write(lp, lineage)
        with self.assertRaisesRegex(ValueError, "changed a frozen condition"):
            scan()

    def test_stale_report_cannot_freeze_modified_artifact(self):
        cohort, report = self.scan()
        Path(self.cohort["artifacts"][1]["candidate"]["path"]).write_bytes(b"later modification")
        with self.assertRaisesRegex(ValueError, "Hash mismatch"):
            F.save_reconciliation(cohort, report, self.root / "stale")
        self.assertFalse((self.root / "stale/FINAL_COHORT.json").exists())

    def test_missing_causes_separate_budget_infrastructure_timeout_and_no_file(self):
        Path(self.cohort["artifacts"][2]["candidate"]["path"]).unlink()
        self.pi_receipt["artifact_status"] = "missing"
        cases = [
            ("provider_error", [{"reason": "Provider request cap reached"}], "budget_cap:Provider request cap reached"),
            ("provider_error", [{"reason": "Cell dollar cap cannot admit next request"}], "budget_cap:Cell dollar cap cannot admit next request"),
            ("provider_error", [{"reason": "URLError"}], "infrastructure:URLError"),
            ("provider_error", [{"reason": "HTTPError", "upstream_http_status": 503, "phase": "generate_content"}], "infrastructure:HTTPError"),
            ("timeout", [], "timeout"),
            ("process_completed", [], "ended_without_file")]
        for status, denials, expected in cases:
            with self.subTest(expected=expected):
                self.pi_receipt["status"] = status
                self.ledger["denials"] = denials
                self.write(self.pi_receipt_path, self.pi_receipt)
                self.write(self.ledger_path, self.ledger)
                _, report = self.scan()
                row = report["cells"][2]
                self.assertEqual(row["missing_cause"], expected)
                self.assertEqual(row["missing_cause_evidence"]["gateway_ledger"], self.record(self.ledger_path))
                self.assertEqual(report["ratable_subset_available"], not expected.startswith("infrastructure:"))
        self.ledger_path.unlink()
        _, report = self.scan()
        self.assertEqual(report["cells"][2]["missing_cause"], "infrastructure:missing_gateway_ledger")
        self.assertEqual(report["cells"][2]["missing_cause_evidence"]["cost_upper_bound_usd"], .75)

    def test_cc_missing_before_call_and_limits_keep_distinct_causes(self):
        Path(self.cohort["artifacts"][1]["candidate"]["path"]).unlink()
        self.cc_receipt["candidate_captured"] = False
        for called, status, stop, expected in [
            (False, "INFRASTRUCTURE_INTERRUPTED", None, "infrastructure:before_model_call"),
            (True, "INFRASTRUCTURE_INTERRUPTED", None, "infrastructure:runner_interrupted"),
            (True, "TERMINAL", "observed_output_token_budget", "budget_cap:observed_output_token_budget"),
            (True, "TERMINAL", "wall_time_budget", "timeout"),
            (True, "TERMINAL", "native_result", "ended_without_file")]:
            self.cc_receipt.update(model_call_performed=called, status=status, stop_reason=stop)
            self.write(self.cc_receipt_path, self.cc_receipt)
            _, report = self.scan()
            self.assertEqual(report["cells"][1]["missing_cause"], expected)

    def test_pi_process_completion_with_native_length_is_response_cap(self):
        Path(self.cohort["artifacts"][2]["candidate"]["path"]).unlink()
        self.pi_receipt.update(status="process_completed", artifact_status="missing", native_stop_reason="length")
        self.ledger["requests"] = [{"call": 19, "http_status": 200,
            "provider_finish_reason": "MAX_TOKENS", "max_output_tokens": 1055}]
        self.write(self.pi_receipt_path, self.pi_receipt)
        self.write(self.ledger_path, self.ledger)
        _, report = self.scan()
        row = report["cells"][2]
        self.assertEqual(row["missing_cause"], "budget_cap:native_response_output_limit")
        self.assertEqual(row["execution_status"], "process_completed")
        self.assertEqual(row["missing_cause_evidence"]["native_stop_reason"], "length")
        self.assertEqual(row["missing_cause_evidence"]["last_request"]["max_output_tokens"], 1055)
        self.assertTrue(report["ratable_subset_available"])
        # A failed provider response must not inherit the clean response-cap verdict.
        self.ledger["requests"][0].update(http_status=503, provider_finish_reason=None)
        self.write(self.ledger_path, self.ledger)
        _, report = self.scan()
        self.assertTrue(report["cells"][2]["missing_cause"].startswith("infrastructure:"))
        self.assertFalse(report["ratable_subset_available"])

    def test_cc_native_output_limit_is_budget_not_infrastructure(self):
        Path(self.cohort["artifacts"][1]["candidate"]["path"]).unlink()
        self.cc_receipt.update(candidate_captured=False, status="TERMINAL", exit_code=1,
                               stop_reason="native_result", model_call_performed=True,
                               native_result={"subtype": "success", "is_error": True,
                                   "terminal_reason": "api_error", "api_error": "max_output_tokens",
                                   "num_turns": 5,
                                   "result": "API Error: Claude's response exceeded the 16384 output token maximum."})
        self.write(self.cc_receipt_path, self.cc_receipt)
        _, report = self.scan()
        row = report["cells"][1]
        self.assertEqual(row["state"], "MISSING_OUTPUT")
        self.assertEqual(row["missing_cause"], "budget_cap:native_response_output_limit")
        self.assertEqual(row["missing_cause_evidence"]["native_api_error"], "max_output_tokens")
        self.assertEqual(row["missing_cause_evidence"]["native_terminal_reason"], "api_error")
        self.assertTrue(report["ratable_subset_available"])
        self.assertEqual(report["infrastructure_items_awaiting_disposition"], [])
        # A different native error must still require infrastructure disposition.
        self.cc_receipt["native_result"]["api_error"] = "overloaded_error"
        self.write(self.cc_receipt_path, self.cc_receipt)
        _, report = self.scan()
        self.assertEqual(report["cells"][1]["missing_cause"], "infrastructure:native_error_or_incomplete_result")
        self.assertFalse(report["ratable_subset_available"])

    def test_infrastructure_exclusion_requires_exact_hash_bound_disposition(self):
        Path(self.cohort["artifacts"][2]["candidate"]["path"]).unlink()
        self.pi_receipt.update(status="provider_error", artifact_status="missing")
        self.ledger["denials"] = [{"reason": "URLError"}]
        self.write(self.pi_receipt_path, self.pi_receipt)
        self.write(self.ledger_path, self.ledger)
        _, report = self.scan()
        row = report["cells"][2]
        self.assertFalse(report["ratable_subset_available"])
        entry = {k: row[k] for k in ("item_id", "task_id", "configuration_id", "receipt_sha256", "missing_cause")}
        entry.update(gateway_ledger=row["missing_cause_evidence"]["gateway_ledger"],
                     disposition="EXCLUDE_INFRASTRUCTURE_NOT_SOLVER_FAILURE")
        disposition = self.write("DISPOSITION.json", {"planned_cohort": self.record(self.cohort_path), "excluded_cells": [entry]})
        lineage = {"planned_cohort": self.record(self.cohort_path), "infrastructure_disposition": self.record(disposition),
            "configurations": {config: [{"condition": self.cohort["configurations"][config]["planned_condition_snapshot"],
                "runner": self.record(self.runner), "output_root": self.cohort["configurations"][config]["output_root"],
                "task_ids": [self.task_id]}] for config in (F.CC, F.PI)}}
        lp = self.write("LINEAGE.json", lineage)
        cohort, report = F.reconcile(self.cohort_path, self.sha(self.cohort_path), pi_index=self.pi_index,
            cc_runner=self.runner, pi_runner=self.runner, lineage_record=self.record(lp))
        self.assertTrue(report["ratable_subset_available"])
        frozen = F.save_reconciliation(cohort, report, self.root / "infra_subset", ratable_subset=True)
        self.assertEqual(json.loads(Path(frozen["path"]).read_text())["infrastructure_disposition"], self.record(disposition))

    def recovered_fixture(self):
        cell = self.pi_receipt_path.parent
        Path(self.cohort["artifacts"][2]["candidate"]["path"]).unlink()
        original = {**self.pi_receipt, "status": "running", "started_at": "2026-11-11T20:00:00+00:00"}
        original.pop("finished_at")
        op = self.write(cell / "receipt_before_host_supervision_recovery.json", original)
        observer = self.root / "observer.py"
        observer.write_text("# synthetic observer; no model calls\n")
        self.pi_receipt.update(status="recovered_native_terminal", artifact_status="missing",
            started_at=original["started_at"], finished_at="2026-11-11T20:20:00+00:00", elapsed_seconds=1200,
            provider_requests=40, accounted_usd=.6)
        initial = self.write(cell / "receipt_before_recovered_identity_correction.json", self.pi_receipt)
        sessiondir = cell / "pi-sessions_recovered"
        sessiondir.mkdir()
        events = [{"type": "model_change", "provider": "allen-google-veribench", "modelId": "gemini-3.8-flash"},
                  {"type": "thinking_level_change", "thinkingLevel": "high"},
                  {"type": "message", "message": {"role": "assistant", "model": "gemini-3.8-flash",
                                                   "provider": "allen-google-veribench"}}]
        session = sessiondir / "session.jsonl"
        session.write_text("\n".join(json.dumps(e) for e in events) + "\n")
        identity = self.write(cell / "recovered_session_identity_evidence.json", [
            {"session_file": str(session), "session_sha256": self.sha(session), "event": e} for e in events[:2]])
        self.pi_receipt["supervision_recovery"] = {
            "original_receipt_sha256": self.sha(op), "initial_recovered_receipt_sha256": self.sha(initial),
            "observer_sha256": self.sha(observer), "native_identity_evidence_sha256": self.sha(identity),
            "original_deadline_utc": "2026-11-11T20:30:00+00:00"}
        self.write(self.pi_receipt_path, self.pi_receipt)
        self.ledger.update(accounted_usd=.6, requests=[{"call": i, "http_status": 200,
            "provider_finish_reason": "STOP"} for i in range(1, 41)],
            denials=[{"reason": "Provider request cap reached"}])
        self.write(self.ledger_path, self.ledger)
        incident = self.write("INCIDENT.json", {"no_task_restarts": True,
            "original_deadlines_enforced_by_detached_observer": True, "observer_sha256": self.sha(observer),
            "recovered_outcomes": [{"task_id": self.task_id, "status": "recovered_native_terminal",
                                    "artifact_status": "missing"}]})
        entry = {"item_id": self.cohort["artifacts"][2]["item_id"], "task_id": self.task_id,
            "configuration_id": F.PI, "receipt": self.record(self.pi_receipt_path),
            "original_receipt": self.record(op), "initial_recovered_receipt": self.record(initial),
            "observer": self.record(observer), "identity_evidence": self.record(identity),
            "incident": self.record(incident), "gateway_ledger": self.record(self.ledger_path),
            "native_sessions": [self.record(session)]}
        lineage = {"planned_cohort": self.record(self.cohort_path), "supervision_recovery_records": [entry],
            "configurations": {config: [{"condition": self.cohort["configurations"][config]["planned_condition_snapshot"],
                "runner": self.record(self.runner), "output_root": self.cohort["configurations"][config]["output_root"],
                "task_ids": [self.task_id]}] for config in (F.CC, F.PI)}}
        lp = self.write("RECOVERY_LINEAGE.json", lineage)
        def scan():
            self.write(lp, lineage)
            return F.reconcile(self.cohort_path, self.sha(self.cohort_path), pi_index=self.pi_index,
                cc_runner=self.runner, pi_runner=self.runner, lineage_record=self.record(lp))
        return lineage, entry, scan

    def test_recovery_preserves_cap_outcome_and_requires_incident_disposition(self):
        lineage, entry, scan = self.recovered_fixture()
        _, unbound = self.scan()
        self.assertEqual(unbound["cells"][2]["state"], "INVALID_PROVENANCE")
        cohort, report = scan()
        row = report["cells"][2]
        self.assertEqual(row["state"], "MISSING_OUTPUT")
        self.assertEqual(row["missing_cause"], "infrastructure:host_supervision_incident")
        self.assertEqual(row["missing_cause_evidence"]["observed_procedure_outcome"],
                         "budget_cap:Provider request cap reached")
        self.assertFalse(row["solver_failure_attributable"])
        self.assertFalse(report["ratable_subset_available"])
        self.assertIsNone(F.save_reconciliation(cohort, report, self.root / "unapproved", ratable_subset=True))
        excluded = {k: row[k] for k in ("item_id", "task_id", "configuration_id", "receipt_sha256", "missing_cause")}
        excluded.update(gateway_ledger=entry["gateway_ledger"], disposition="EXCLUDE_INFRASTRUCTURE_NOT_SOLVER_FAILURE")
        disposition = self.write("RECOVERY_DISPOSITION.json", {
            "planned_cohort": self.record(self.cohort_path), "excluded_cells": [excluded]})
        lineage["infrastructure_disposition"] = self.record(disposition)
        cohort, report = scan()
        self.assertTrue(report["ratable_subset_available"])
        # Even after successful reconciliation, changed session bytes must block freezing.
        session = Path(entry["native_sessions"][0]["path"])
        original = session.read_bytes()
        session.write_bytes(original + b"{}\n")
        with self.assertRaisesRegex(ValueError, "Hash mismatch"):
            F.save_reconciliation(cohort, report, self.root / "stale_recovery", ratable_subset=True)
        session.write_bytes(original)
        frozen = F.save_reconciliation(cohort, report, self.root / "approved_recovery", ratable_subset=True)
        self.assertEqual(json.loads(Path(frozen["path"]).read_text())["expected_artifacts"], 2)

    def test_recovery_rejects_changed_start_deadline_effort_and_ledger_bounds(self):
        _, entry, scan = self.recovered_fixture()
        saved = copy.deepcopy(self.pi_receipt)
        for field, value, reason in [("started_at", "2026-11-11T20:01:00+00:00", "original execution"),
                                     ("provider_requests", 41, "request count"),
                                     ("accounted_usd", .8, "cost exceeds")]:
            with self.subTest(field=field):
                self.pi_receipt = {**saved, field: value}
                self.write(self.pi_receipt_path, self.pi_receipt)
                entry["receipt"] = self.record(self.pi_receipt_path)
                _, report = scan()
                self.assertEqual(report["cells"][2]["state"], "INVALID_PROVENANCE")
                self.assertIn(reason, report["cells"][2]["reason"])
        self.pi_receipt = copy.deepcopy(saved)
        self.pi_receipt["supervision_recovery"]["original_deadline_utc"] = "2026-11-11T20:31:00+00:00"
        self.write(self.pi_receipt_path, self.pi_receipt)
        entry["receipt"] = self.record(self.pi_receipt_path)
        _, report = scan()
        self.assertIn("original deadline", report["cells"][2]["reason"])
        self.pi_receipt = copy.deepcopy(saved)
        session = Path(entry["native_sessions"][0]["path"])
        events = [json.loads(line) for line in session.read_text().splitlines()]
        events[1]["thinkingLevel"] = "low"
        session.write_text("\n".join(json.dumps(e) for e in events) + "\n")
        identity = Path(entry["identity_evidence"]["path"])
        self.write(identity, [{"session_file": str(session), "session_sha256": self.sha(session), "event": e}
                              for e in events[:2]])
        entry["native_sessions"] = [self.record(session)]
        entry["identity_evidence"] = self.record(identity)
        self.pi_receipt["supervision_recovery"]["native_identity_evidence_sha256"] = self.sha(identity)
        self.write(self.pi_receipt_path, self.pi_receipt)
        entry["receipt"] = self.record(self.pi_receipt_path)
        _, report = scan()
        self.assertIn("native effort mismatch", report["cells"][2]["reason"])

    def test_recovery_metadata_cannot_bypass_incident_gate_with_ordinary_status(self):
        _, entry, scan = self.recovered_fixture()
        for status in ("timeout", "process_completed", "running"):
            with self.subTest(status=status):
                self.pi_receipt["status"] = status
                self.write(self.pi_receipt_path, self.pi_receipt)
                entry["receipt"] = self.record(self.pi_receipt_path)
                _, report = scan()
                self.assertEqual(report["cells"][2]["state"], "INVALID_PROVENANCE")
                self.assertIn("explicit terminal status", report["cells"][2]["reason"])
                self.assertFalse(report["ratable_subset_available"])


if __name__ == "__main__":
    unittest.main()
