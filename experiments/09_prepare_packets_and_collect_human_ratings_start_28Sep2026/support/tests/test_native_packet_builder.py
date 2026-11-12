"""Synthetic checks for byte-preserving, blinded, versioned packet assembly."""

import csv
import copy
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest
from zipfile import ZipFile


EXP = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "native_packet_builder", EXP / "support/scripts/native_packet_generation/build_packet.py")
BUILDER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BUILDER)


class NativePacketBuilderTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.addCleanup(self.temporary.cleanup)
        artifacts = []
        for index in range(4):
            tid = f"source_task_{index // 2}"
            py = self.root / f"{tid}.py"
            gold = self.root / f"{tid}_reference.lean"
            candidate = self.root / f"secret_solver_{index}.lean"
            py.write_bytes(b"def f(x):\n    return x\n")
            gold.write_bytes(b"-- original reference\r\ntheorem reference : True := by trivial\r\n")
            candidate.write_bytes(b"" if index == 3 else f"-- unchanged candidate {index}\r\n".encode())
            file_record = lambda p: {"path": str(p), "sha256": hashlib.sha256(p.read_bytes()).hexdigest()}
            artifacts.append({
                "task_id": tid, "task_description": f"Example operation {index // 2}",
                "item_id": f"native-round-1__item{index + 1:03d}",
                "configuration_id": f"private_config_{index % 2}",
                "python": file_record(py), "gold": file_record(gold),
                "candidate": {**file_record(candidate), "status": "empty" if index == 3 else "nonempty"},
                "provenance": {"old_item_id": f"historical_{index}", "process_status": "timeout" if index == 2 else "terminal"},
            })
        self.cohort = {
            "schema_version": 1, "round_id": "native-round-1", "shuffle_seed": "fixed-seed",
            "status": "FINAL_FULL_COHORT", "buildable": True,
            "expected_artifacts": 4,
            "configurations": {"private_config_0": {"model": "Claude Fable", "harness": "Claude Code"},
                               "private_config_1": {"model": "GPT Astra", "harness": "Codex"}},
            "artifacts": artifacts,
        }
        self.manifest = self.root / "cohort.json"
        self.save()

    def save(self):
        self.manifest.write_text(json.dumps(self.cohort))

    def build(self, name="build", **kwargs):
        return BUILDER.build_packet(self.manifest, self.root / name,
                                    rater_name="Test Rater", rater_id="TEST1",
                                    sheet_url="https://docs.google.com/spreadsheets/d/synthetic/edit", **kwargs)

    def test_exact_bytes_blank_responses_schema_and_private_join(self):
        receipt = self.build()
        self.assertEqual(receipt["artifact_count"], 4)
        self.assertEqual(receipt["empty_artifact_count"], 1)
        with ZipFile(receipt["archive_path"]) as archive:
            rows = list(csv.DictReader(io.StringIO(archive.read("ratings.csv").decode())))
            self.assertEqual(list(rows[0]), BUILDER.COLUMNS)
            for row in rows:
                self.assertEqual(row["rater_name"], "Test Rater")
                self.assertEqual(row["rater_id"], "TEST1")
                self.assertTrue(all(row[field] == "" for field in BUILDER.COLUMNS[5:]))
            for join in receipt["artifact_joins"]:
                self.assertEqual(archive.read(join["candidate_file"]), Path(join["source_paths"]["candidate"]).read_bytes())
                self.assertEqual(archive.read(f"{join['task_folder']}/python_source/source.py"), Path(join["source_paths"]["python"]).read_bytes())
                self.assertEqual(archive.read(f"{join['task_folder']}/gold_lean/reference.lean"), Path(join["source_paths"]["gold"]).read_bytes())
            self.assertEqual(archive.read("human_judgements_prompt.md"),
                             (EXP / "rating_task_packet/human_judgements_prompt.md").read_bytes())
            self.assertEqual(archive.read("RATING_FORM_GUIDE.md"),
                             (EXP / "rating_task_packet/RATING_FORM_GUIDE.md").read_bytes())
            self.assertNotIn("ASSEMBLY_RECEIPT.json", archive.namelist())
            self.assertNotIn("YOUR_RATING_SHEET.txt", archive.namelist())
            self.assertIn(b"empty solver output", archive.read("START_HERE.md"))
            labels = "\n".join(archive.namelist()) + archive.read("ratings.csv").decode()
            for token in ("secret_solver", "private_config", "Claude", "Astra", "Codex"):
                self.assertNotIn(token, labels)
            for line in archive.read("FILES.sha256").decode().splitlines():
                expected, name = line.split("  ", 1)
                self.assertEqual(expected, hashlib.sha256(archive.read(name)).hexdigest())

    def test_repeat_build_is_deterministic_and_subset_keeps_ids_and_paths(self):
        full = self.build("full")
        repeat = self.build("repeat")
        self.assertEqual(full["archive_sha256"], repeat["archive_sha256"])
        subset = self.build("subset", task_ids=["source_task_1"])
        self.assertEqual((subset["task_count"], subset["artifact_count"]), (1, 2))
        full_joins = {r["item_id"]: r for r in full["artifact_joins"]}
        for row in subset["artifact_joins"]:
            self.assertEqual(row, full_joins[row["item_id"]])

    def test_filtered_cohort_retains_original_task_and_candidate_paths(self):
        full = self.build("full")
        original_path = self.root / "planned_complete.json"
        original_path.write_bytes(self.manifest.read_bytes())
        planned = copy.deepcopy(self.cohort)
        # Remove an entire task and the earlier shuffled candidate of the other
        # task, so recalculating either ordinal would incorrectly move a path.
        layout = BUILDER.display_layout(planned["artifacts"], planned["shuffle_seed"])
        kept = next(a for a in planned["artifacts"] if layout[a["item_id"]]["candidate_file"].endswith("agent_2.lean")
                    and layout[a["item_id"]]["task_folder"].startswith("task_02_"))
        self.cohort.update(artifacts=[kept], expected_artifacts=1,
            status="FINAL_RATABLE_SUBSET",
            planned_cohort={"path": str(original_path), "sha256": hashlib.sha256(original_path.read_bytes()).hexdigest()},
            display_layout=layout, excluded_item_ids=[a["item_id"] for a in planned["artifacts"] if a != kept])
        self.save()
        subset = self.build("filtered")
        with ZipFile(subset["archive_path"]) as archive:
            self.assertIn(b"File numbers can skip", archive.read("START_HERE.md"))
        expected = next(j for j in full["artifact_joins"] if j["item_id"] == kept["item_id"])
        self.assertEqual(subset["artifact_joins"], [expected])
        self.cohort["display_layout"][kept["item_id"]]["candidate_file"] = "task_01_fake/agent_lean/agent_1.lean"
        self.save()
        with self.assertRaisesRegex(ValueError, "Frozen display layout changed"):
            self.build("tampered")

    def test_refuses_overwrite_and_preserves_existing_archive(self):
        receipt = self.build()
        before = Path(receipt["archive_path"]).read_bytes()
        with self.assertRaisesRegex(ValueError, "Refusing to overwrite"):
            self.build()
        self.assertEqual(before, Path(receipt["archive_path"]).read_bytes())

    def test_hash_mismatch_and_missing_file_fail_before_creating_build(self):
        candidate = Path(self.cohort["artifacts"][0]["candidate"]["path"])
        original = candidate.read_bytes()
        candidate.write_bytes(original + b"changed")
        with self.assertRaisesRegex(ValueError, "hash mismatch"):
            self.build()
        self.assertFalse((self.root / "build").exists())
        candidate.unlink()
        with self.assertRaisesRegex(ValueError, "Missing source"):
            self.build()

    def test_empty_status_and_unknown_assignment_are_not_silently_repaired(self):
        self.cohort["artifacts"][0]["candidate"]["status"] = "empty"
        self.save()
        with self.assertRaisesRegex(ValueError, "contradicts bytes"):
            self.build()
        self.cohort["artifacts"][0]["candidate"]["status"] = "nonempty"
        self.save()
        with self.assertRaisesRegex(ValueError, "Unknown or empty"):
            self.build(task_ids=["unknown_task"])
        with self.assertRaisesRegex(ValueError, "Duplicate assigned"):
            self.build(task_ids=["source_task_1", "source_task_1"])

    def test_rejects_identity_in_generated_names_and_non_neutral_item_ids(self):
        for artifact in self.cohort["artifacts"][:2]:
            artifact["task_description"] = "Codex example"
        self.save()
        with self.assertRaisesRegex(ValueError, "identity"):
            self.build()
        self.cohort["artifacts"][0]["item_id"] = "native-round-1__claude01"
        self.save()
        with self.assertRaisesRegex(ValueError, "neutral"):
            self.build()

    def test_rejects_duplicate_cells_and_known_identity_without_redacting(self):
        self.cohort["artifacts"][1]["configuration_id"] = "private_config_0"
        self.save()
        with self.assertRaisesRegex(ValueError, "Duplicate task/configuration"):
            self.build()
        self.cohort["artifacts"][1]["configuration_id"] = "private_config_1"
        candidate = Path(self.cohort["artifacts"][0]["candidate"]["path"])
        original = b"-- Generated by Claude Fable\n"
        candidate.write_bytes(original)
        self.cohort["artifacts"][0]["candidate"]["sha256"] = hashlib.sha256(original).hexdigest()
        self.save()
        with self.assertRaisesRegex(ValueError, "identity"):
            self.build()
        self.assertEqual(candidate.read_bytes(), original)
        self.assertFalse((self.root / "build").exists())

    def test_requires_final_cohort_and_stem_blinding_preserves_lean_pi(self):
        self.cohort["buildable"] = False
        self.save()
        with self.assertRaisesRegex(ValueError, "finalized, buildable"):
            self.build()
        self.cohort["buildable"] = True
        candidate = Path(self.cohort["artifacts"][0]["candidate"]["path"])
        for text, rejected in [(b"-- written by Claude\n", True),
                               (b"-- generated by Pi\n", True),
                               (b"-- Ordinary Lean Pi type and pi notation\n", False)]:
            candidate.write_bytes(text)
            self.cohort["artifacts"][0]["candidate"]["sha256"] = hashlib.sha256(text).hexdigest()
            self.save()
            if rejected:
                with self.assertRaisesRegex(ValueError, "recognizable solver identity"):
                    self.build()
                self.assertEqual(candidate.read_bytes(), text)
            else:
                self.build()

    def test_sheet_readback_exact_match_and_mismatch_release_gate(self):
        receipt = self.build()
        build_dir = Path(receipt["archive_path"]).parent
        archive_before = Path(receipt["archive_path"]).read_bytes()
        values = list(csv.reader(io.StringIO((build_dir / "rating_task_packet/ratings.csv").read_text())))
        readback = self.root / "sheet_readback.json"
        data = {"sheet_url": receipt["sheet_url"], "range": "Sheet1!A1:K5", "values": values}
        readback.write_text(json.dumps(data))
        self.assertFalse(receipt["release_ready"])
        check = BUILDER.verify_sheet_readback(build_dir, readback)
        self.assertTrue(check["sheet_csv_equal"])
        self.assertTrue(json.loads((build_dir / "ASSEMBLY_RECEIPT.json").read_text())["release_ready"])
        data["values"][1][0] = "Different Rater"
        readback.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, "release is held"):
            BUILDER.verify_sheet_readback(build_dir, readback)
        self.assertFalse(json.loads((build_dir / "ASSEMBLY_RECEIPT.json").read_text())["release_ready"])
        self.assertEqual(Path(receipt["archive_path"]).read_bytes(), archive_before)


if __name__ == "__main__":
    unittest.main()
