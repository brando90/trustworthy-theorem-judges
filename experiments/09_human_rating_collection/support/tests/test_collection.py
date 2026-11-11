"""Check packet preservation and inherited import rules without reading real ratings."""
import contextlib
import csv
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
from zipfile import ZipFile

EXPERIMENT = Path(__file__).resolve().parents[2]
ROOT = EXPERIMENT.parents[1]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    with patch.object(sys, "path", [str(path.parent), *sys.path]):
        spec.loader.exec_module(module)
    return module


BUILDER = load("collection_packet", EXPERIMENT / "scripts/make_team_packet.py")
IMPORTER = load("collection_import", EXPERIMENT / "scripts/legacy/import_rating_sheet.py")
RELEASE = load("collection_release", EXPERIMENT / "scripts/legacy/packet_release.py")
WARMUP = load("collection_warmup", EXPERIMENT / "scripts/legacy/score_warmup.py")
try:
    ASSIGNER = load("collection_assign", EXPERIMENT / "scripts/legacy/assign_setN_folders.py")
except ModuleNotFoundError as error:
    if error.name != "numpy":
        raise
    ASSIGNER = None


def check_archive(path, expected_rows):
    with ZipFile(path) as archive:
        members = set(archive.namelist())
        listing = archive.read("FILES.sha256").decode().splitlines()
        listed = set()
        for line in listing:
            digest, name = line.split("  ", 1)
            if hashlib.sha256(archive.read(name)).hexdigest() != digest:
                raise AssertionError(f"Archive hash mismatch: {name}")
            listed.add(name)
        if listed != members - {"FILES.sha256"}:
            raise AssertionError("Archive manifest is not exhaustive")
        rows = list(csv.DictReader(io.StringIO(archive.read("ratings.csv").decode())))
        if len(rows) != expected_rows:
            raise AssertionError("Unexpected answer-sheet row count")
        ids = [row["item_id"] for row in rows]
        if len(set(ids)) != len(ids):
            raise AssertionError("Duplicate item identifiers")
        for row in rows:
            candidate = f"{row['task_folder']}/agent_lean/{row['candidate_file']}"
            if candidate not in members or row["item_id"] != Path(candidate).stem:
                raise AssertionError("Answer sheet does not map to candidates")
            if row["rater_id"] or row["final_score_0_5"]:
                raise AssertionError("Team sheet must be blank")
        if "your personal rating sheet" in archive.read("Rating_Instructions.md").decode():
            raise AssertionError("Coordinator's sheet link leaked into team instructions")
        return members


class PacketTests(unittest.TestCase):
    def fixture(self, root):
        data = {
            "START_HERE.md": b"# Start\n\n## Assistance and reference problems\n\nRate independently.\n",
            "Rating_Instructions.md": b"# Rubric\n\nOpen [your personal rating sheet](https://example.invalid/private).\n",
            "Files_To_Rate01/python_source/example.py": b"# Synthetic packaging fixture\n",
            "Files_To_Rate01/gold_lean/example.lean": b"-- Synthetic packaging fixture, not a proof\n",
        }
        for n in range(1, 6):
            data[f"Files_To_Rate01/agent_lean/agent_file{n:02d}.lean"] = f"-- Synthetic candidate {n}\n".encode()
        for name, content in data.items():
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(content)
        manifest = "".join(f"{hashlib.sha256(content).hexdigest()}  {name}\n" for name, content in sorted(data.items())).encode()
        (root / "FILES.sha256").write_bytes(manifest)
        return data, hashlib.sha256(manifest).hexdigest()

    def build(self, root, output, manifest_digest, extra_args=()):
        with patch.object(BUILDER, "MANIFEST_SHA256", manifest_digest), patch.object(
            sys, "argv", ["make_team_packet.py", str(root), str(output), "--folders", "1", *extra_args]
        ), contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            BUILDER.main()

    def test_packet_preserves_files_and_blank_sheet(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "source"
            data, digest = self.fixture(root)
            output = Path(temp) / "packet.zip"
            self.build(root, output, digest)
            check_archive(output, 5)
            with ZipFile(output) as archive:
                for name, content in data.items():
                    if name.startswith("Files_To_Rate"):
                        self.assertEqual(archive.read(name), content)
            with self.assertRaises(FileExistsError):
                self.build(root, output, digest)

    def test_personalized_team_packet_name_and_item_columns_align(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "source"
            _, digest = self.fixture(root)
            output = Path(temp) / "named.zip"
            self.build(root, output, digest, ["--rater", "T01"])
            with ZipFile(output) as archive:
                reader = csv.DictReader(io.StringIO(archive.read("ratings.csv").decode()))
                self.assertEqual(reader.fieldnames[:2], ["rater_name", "rater_id"])
                rows = list(reader)
                self.assertEqual(len(rows), 5)
                for row in rows:
                    self.assertEqual(row["rater_name"], "Rylan Schaeffer")
                    self.assertEqual(row["rater_id"], "T01")
                    self.assertEqual(row["task_folder"], "Files_To_Rate01")
                    self.assertEqual(row["candidate_file"], row["item_id"] + ".lean")
                    self.assertEqual(row["final_score_0_5"], "")
                    self.assertEqual(row["ai_assisted_rating_attestation"], "")
            with self.assertRaises(SystemExit):
                self.build(root, Path(temp) / "unknown.zip", digest, ["--rater", "UNKNOWN"])

    def test_rejects_changed_candidate(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "source"
            _, digest = self.fixture(root)
            (root / "Files_To_Rate01/agent_lean/agent_file01.lean").write_text("changed")
            output = Path(temp) / "packet.zip"
            with self.assertRaises(SystemExit):
                self.build(root, output, digest)
            self.assertFalse(output.exists())

    def test_rejects_changed_manifest(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "source"
            _, digest = self.fixture(root)
            with (root / "FILES.sha256").open("ab") as stream:
                stream.write(b"\n")
            with self.assertRaises(SystemExit):
                self.build(root, Path(temp) / "packet.zip", digest)

    @unittest.skipUnless((ROOT / "private/original").is_dir(), "Coordinator's original packet is private")
    def test_real_packet_all_folders_preserves_source(self):
        source = ROOT / "private/original"
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp) / "all.zip"
            subprocess.run([sys.executable, str(EXPERIMENT / "scripts/make_team_packet.py"), str(source), str(output)],
                           check=True, capture_output=True, text=True)
            members = check_archive(output, 125)
            with ZipFile(output) as archive:
                for name in members:
                    if name.startswith("Files_To_Rate"):
                        self.assertEqual(archive.read(name), (source / name).read_bytes())


class LegacyImportTests(unittest.TestCase):
    def check(self, rows, allowed=None, packet="setN"):
        text = "rater_id,item_id,final_score_0_5\n" + rows
        return IMPORTER.check(text, "TEST", {"N01_a", "N01_b"}, {"N01"} if allowed is None else allowed, packet)

    def test_private_root_is_new_repository(self):
        expected = (ROOT / "private/09_human_rating_collection/upstream_source"
                    / "experiments/102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml")
        self.assertEqual(IMPORTER.EXP, expected)
        self.assertEqual(RELEASE.EXP, expected)
        self.assertEqual(WARMUP.EXP, expected)

    def test_accepts_synthetic_rating_without_writing(self):
        rows, errors, warnings, name, reference_issues = self.check("TEST,N01_a,3\n")
        self.assertFalse(reference_issues)
        self.assertFalse(errors)
        self.assertEqual(rows[0]["final_score_0_5"], 3)
        self.assertTrue(warnings)  # Other assigned item is still missing.
        self.assertEqual(name, "TEST")

    def test_rejects_invalid_or_duplicate_scores(self):
        for text in ("TEST,N01_a,6\n", "TEST,N01_a,2.5\n", "TEST,N01_a,nan\n",
                     "TEST,N01_a,3\nTEST,N01_a,4\n", ",N01_a,3\n"):
            with self.subTest(text=text):
                self.assertTrue(self.check(text)[1])

    def test_rejects_unassigned_folder(self):
        self.assertTrue(self.check("TEST,N01_a,3\n", allowed={"N02"})[1])

    def test_rejects_incomplete_warmup(self):
        self.assertTrue(self.check("TEST,N01_a,3\n", packet="warmup")[1])

    def test_renamed_team_ids_are_not_legacy_ids(self):
        self.assertTrue(self.check("TEST,agent_file01,3\n")[1])


class CurrentProtocolTests(unittest.TestCase):
    @unittest.skipUnless(RELEASE.STATUS.is_file(), "Pinned inherited packets are private")
    def test_legacy_packets_preserve_release_files_and_refuse_overwrite(self):
        with tempfile.TemporaryDirectory() as temp:
            for packet in ("setN", "warmup"):
                with self.subTest(packet=packet):
                    output = Path(temp) / packet
                    command = [sys.executable, str(EXPERIMENT / "scripts/legacy/make_rater_zip.py"),
                               "--packet", packet, "--rater", "SYNTHETIC",
                               "--sheet-url", "https://docs.google.com/spreadsheets/d/synthetic_test_sheet_id_00001/edit",
                               "--share-email", "rater@example.invalid", "--out-dir", str(output)]
                    if packet == "setN":
                        command += ["--folders", "N01"]
                    subprocess.run(command, check=True, capture_output=True, text=True)
                    archive_path = next(output.glob("*.zip"))
                    original_bytes = archive_path.read_bytes()
                    receipts = output / "DELIVERY_RECEIPTS.jsonl"
                    original_receipt = receipts.read_bytes()
                    receipt = json.loads(original_receipt)
                    self.assertEqual(receipt["zip_sha256"], hashlib.sha256(original_bytes).hexdigest())
                    top = f"VeriBench_{packet}_SYNTHETIC/"
                    with ZipFile(archive_path) as archive:
                        listed = set()
                        for line in archive.read(top + "FILES.sha256").decode().splitlines():
                            digest, name = line.split("  ", 1)
                            data = archive.read(top + name)
                            self.assertEqual(hashlib.sha256(data).hexdigest(), digest)
                            listed.add(top + name)
                            if name != "YOUR_RATING_SHEET.txt":
                                self.assertEqual(data, (RELEASE.PACKETS[packet] / name).read_bytes())
                        self.assertEqual(listed, set(archive.namelist()) - {top + "FILES.sha256"})
                    repeat = subprocess.run(command, capture_output=True, text=True)
                    self.assertNotEqual(repeat.returncode, 0)
                    self.assertIn("FileExistsError", repeat.stderr)
                    self.assertEqual(archive_path.read_bytes(), original_bytes)
                    self.assertEqual(receipts.read_bytes(), original_receipt)

    @unittest.skipIf(ASSIGNER is None, "Assignment utility requires numpy")
    def test_delivered_assignments_stay_pinned(self):
        raters = [{"id": rid, "pool": pool, "pledge": 4, "left": 4, "status": "yes"}
                  for rid, pool in (("LEFT", "team"), ("RIGHT", "vendor"))]
        plan = ASSIGNER.assign(["N01", "N02", "N03", "N04"], raters,
                               pinned={"N01": ["LEFT"], "N02": ["RIGHT"]})
        self.assertEqual(plan["N01"][0], "LEFT")
        self.assertEqual(plan["N02"][0], "RIGHT")
        self.assertTrue(all(set(ids) == {"LEFT", "RIGHT"} for ids in plan.values()))
        self.assertTrue(all(r["left"] == 0 for r in raters))

    def test_release_checks_status_receipt_and_packet_bytes(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            packet = root / "packet"
            packet.mkdir()
            candidate = packet / "synthetic.txt"
            candidate.write_bytes(b"synthetic release fixture")
            listing = packet / "FILES.sha256"
            listing.write_text(f"{hashlib.sha256(candidate.read_bytes()).hexdigest()}  synthetic.txt\n")
            acceptance = root / "acceptance.txt"
            acceptance.write_bytes(b"synthetic acceptance fixture")
            state = {"status": "HOLD", "reason": "synthetic hold",
                     "files_sha256_digest": hashlib.sha256(listing.read_bytes()).hexdigest(),
                     "acceptance_record": acceptance.name,
                     "acceptance_record_sha256": hashlib.sha256(acceptance.read_bytes()).hexdigest()}
            status = root / "PACKET_STATUS.json"
            with patch.object(RELEASE, "PACKETS", {"setN": packet}):
                status.write_text(json.dumps({"packets": {"setN": state}}))
                with self.assertRaises(SystemExit):
                    RELEASE.require_release("setN", status)
                state["status"] = "RELEASED"
                status.write_text(json.dumps({"packets": {"setN": state}}))
                RELEASE.require_release("setN", status)
                acceptance.write_bytes(b"changed acceptance")
                with self.assertRaises(SystemExit):
                    RELEASE.require_release("setN", status)
                acceptance.write_bytes(b"synthetic acceptance fixture")
                candidate.write_bytes(b"changed candidate")
                with self.assertRaises(SystemExit):
                    RELEASE.require_release("setN", status)

    def test_emailed_csv_import_preserves_raw_bytes_and_route(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = root / "emailed.csv"
            raw = b"rater_id,item_id,final_score_0_5\r\nTEST,N01_a,3\r\nTEST,N01_b,4\r\n"
            source.write_bytes(raw)
            template = root / "template.csv"
            template.write_text("rater_id,item_id,final_score_0_5\n,N01_a,\n,N01_b,\n")
            receipts = root / "delivery.jsonl"
            delivery = {"rater": "TEST", "packet": "setN", "folders": ["N01"],
                        "return_route": "emailed_csv", "thread_id": "synthetic-thread"}
            event = {"rater": "TEST", "packet": "setN", "event": "sent"}
            receipts.write_text(json.dumps(delivery) + "\n" + json.dumps(event) + "\n")
            self.assertEqual(IMPORTER.latest_receipt(receipts, "TEST", "setN"), delivery)
            output = root / "output"
            common = ["--rater", "TEST", "--packet", "setN", "--source-modified", "2026-11-09T00:00:00Z",
                      "--receipts", str(receipts), "--out-dir", str(output)]
            with patch.object(IMPORTER, "TEMPLATES", {"setN": template}), contextlib.redirect_stdout(io.StringIO()):
                with patch.object(sys, "argv", ["import_rating_sheet.py", str(source), "--file-id", "synthetic-sheet", *common]):
                    with self.assertRaises(SystemExit):
                        IMPORTER.main()
                self.assertFalse(output.exists())
                with patch.object(sys, "argv", ["import_rating_sheet.py", "--csv", str(source),
                                                 "--source-message-id", "synthetic-message", *common]):
                    IMPORTER.main()
            snapshots = list((output / "raw").glob("*.csv"))
            self.assertEqual(len(snapshots), 1)
            self.assertEqual(snapshots[0].read_bytes(), raw)
            receipt = json.loads((output / "RECEIPTS.jsonl").read_text())
            self.assertEqual(receipt["rows_rated"], 2)
            self.assertEqual(receipt["source_route"], IMPORTER.CSV_ROUTE)
            self.assertEqual(receipt["sha256_export"], hashlib.sha256(raw).hexdigest())

    def test_personal_sheet_bindings_are_private_and_required(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / "personal_sheet_ids.json"
            with patch.object(IMPORTER, "A1_SHEETS_PATH", path):
                with self.assertRaises(SystemExit):
                    IMPORTER.personal_sheet("setN")
                path.write_text(json.dumps({"setN": "synthetic-sheet"}))
                self.assertEqual(IMPORTER.personal_sheet("setN"), "synthetic-sheet")

    def test_reference_issue_rows_are_not_scores(self):
        rows, errors, warnings, name, issues = IMPORTER.check(
            "rater_id,item_id,final_score_0_5,problem_note\nTEST,W01_a,4,\nTEST,W02_a,N/A,Synthetic reference issue\n",
            "TEST", {"W01_a", "W02_a"}, {"W01", "W02"}, "warmup", {"W02_a"})
        self.assertFalse(errors)
        self.assertEqual([r["item_id"] for r in rows], ["W01_a"])
        self.assertEqual(issues, {"W02_a": "Synthetic reference issue"})
        self.assertEqual(IMPORTER.QUALIFY_TASKS, ("W01",))

    def test_qualification_and_missing_nonqualifying_rows(self):
        self.assertEqual(WARMUP.DEFAULT_QUALIFY, ["W01"])
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            key = root / "synthetic-key.json"
            items = [{"item_id": f"{folder}_{letter}", "expert_mean_0_5": 4,
                      "expert_scores_0_5": [4, 4, 4]} for folder in ("W01", "W02") for letter in "abc"]
            key.write_text(json.dumps({"cutoff_mae_0_5": 1.0, "items": items}))
            manifest = root / "manifest.json"
            manifest.write_text(json.dumps({"sealed_key_sha256": "0" * 64}))
            sheet = root / "synthetic-sheet.csv"
            qualifying = "rater_id,item_id,final_score_0_5\n" + "".join(f"TEST,W01_{x},4\n" for x in "abc")
            sheet.write_text(qualifying + "".join(f"TEST,W02_{x},0\n" for x in "abc"))
            # Release behavior has its own fixture above; never open real sealed key values.
            with patch.object(WARMUP, "MANIFEST", manifest), patch.object(WARMUP, "require_release"):
                with self.assertRaises(SystemExit):
                    WARMUP.main([sheet], ["W01"], key, False)
                output = io.StringIO()
                with contextlib.redirect_stdout(output):
                    WARMUP.main([sheet], ["W01"], key, True, leave_out_expert=1)
                self.assertIn("-> QUALIFIES", output.getvalue())
                self.assertIn("2.00 (would does not qualify)", output.getvalue())
                self.assertIn("leave-one-out", output.getvalue())
                self.assertIn("SYNTHETIC KEY", output.getvalue())
                sheet.write_text(qualifying)
                output = io.StringIO()
                with contextlib.redirect_stdout(output):
                    WARMUP.main([sheet], ["W01"], key, True, allow_missing_nonqualifying=True)
                self.assertIn("-> QUALIFIES", output.getvalue())
                self.assertIn("unavailable", output.getvalue())


if __name__ == "__main__":
    unittest.main()
