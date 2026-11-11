"""Synthetic checks for name enrichment without changing or duplicating ratings."""
import csv
import contextlib
import json
import sys
import importlib.util
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

PATH = Path(__file__).resolve().parents[2] / "scripts/refresh_named_ratings.py"
SPEC = importlib.util.spec_from_file_location("named_ratings", PATH)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class NamedRatingsTests(unittest.TestCase):
    def test_existing_name_is_verified_and_never_duplicated(self):
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "warmup_T01.csv"
            original = b"rater_name,rater_id,item_id,final_score_0_5\nExample Rater,T01,W01a,0\n"
            source.write_bytes(original)
            identities = {"T01": {"rater_name": "Example Rater", "filename_stem": "Example_Rater"}}
            _, data, _ = MODULE.named_export(source, identities)
            reader = csv.DictReader(io.StringIO(data.decode()))
            self.assertEqual(reader.fieldnames[:2], ["rater_name", "rater_id"])
            self.assertEqual(reader.fieldnames.count("rater_name"), 1)
            self.assertEqual(next(reader)["final_score_0_5"], "0")
            self.assertEqual(source.read_bytes(), original)
            source.write_bytes(original.replace(b"Example Rater,T01", b"Wrong Person,T01"))
            with self.assertRaisesRegex(ValueError, "verified identity"):
                MODULE.named_export(source, identities)

    def test_roster_metadata_cannot_fill_or_replace_original_responses(self):
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "warmup_T01.csv"
            original = (b"rater_id,item_id,final_score_0_5,minutes_spent,lean_familiarity,rationale,problem_note\n"
                        b'T01,W01a,0,,none,,"note, with comma"\n'
                        b'T01,W01b,2,4,some,"First line\n# participant note",\n')
            source.write_bytes(original)
            identities = {"T01": {"rater_name": "Example Rater", "filename_stem": "Example_Rater",
                                  "programming_languages_background": "Coordinator coursework claim",
                                  "background_source": "Coordinator report",
                                  "minutes_spent": "60", "lean_familiarity": "fluent",
                                  "rationale": "Invented explanation"}}
            _, data, receipt = MODULE.named_export(source, identities)
            original_reader = csv.DictReader(io.StringIO(original.decode()))
            fields, original_rows = original_reader.fieldnames, list(original_reader)
            exported = csv.DictReader(io.StringIO(data.decode()))
            self.assertEqual(exported.fieldnames, ["rater_name", *fields])
            exported_rows = list(exported)
            self.assertEqual([{field: row[field] for field in fields} for row in exported_rows], original_rows)
            self.assertEqual(exported_rows[0]["minutes_spent"], "")
            self.assertEqual(exported_rows[0]["lean_familiarity"], "none")
            self.assertEqual(exported_rows[0]["rationale"], "")
            self.assertNotIn("background_enrichment", receipt)
            self.assertNotIn("timing_estimates", receipt)
            self.assertEqual(source.read_bytes(), original)

    def test_refresh_ignores_leftover_coordinator_estimate_file(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            inputs, outputs = root / "imports", root / "ratings/analysis"
            inputs.mkdir()
            source = inputs / "warmup_T01.csv"
            original = b"rater_id,item_id,final_score_0_5,minutes_spent\nT01,W01a,0,\n"
            source.write_bytes(original)
            identities = root / "RATER_IDENTITIES.json"
            identities.write_text(json.dumps({"T01": {"rater_name": "Example Rater", "filename_stem": "Example_Rater"}}))
            estimate_file = root / "RATING_TIME_ESTIMATES.json"
            estimate_content = json.dumps({source.name: {"reported_total_minutes": 60, "items": {
                "W01a": {"minutes": 60, "basis": "Coordinator allocation"}}}})
            estimate_file.write_text(estimate_content)
            with patch.object(MODULE, "EXPERIMENT", root), patch.object(sys, "argv", [
                "refresh_named_ratings.py", "--input-dir", str(inputs), "--out-dir", str(outputs),
                "--identities", str(identities)
            ]), contextlib.redirect_stdout(io.StringIO()):
                MODULE.main()
            reader = csv.DictReader(io.StringIO((outputs / "Example_Rater__warmup_T01.csv").read_text()))
            self.assertEqual(reader.fieldnames, ["rater_name", "rater_id", "item_id", "final_score_0_5", "minutes_spent"])
            self.assertEqual(next(reader)["minutes_spent"], "")
            self.assertEqual(estimate_file.read_text(), estimate_content)
            self.assertEqual(source.read_bytes(), original)

    def test_default_refresh_uses_analysis_and_refuses_raw_destination(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            inputs, raw_dir = root / "imports", root / "ratings"
            inputs.mkdir()
            raw_dir.mkdir()
            (inputs / "warmup_T01.csv").write_text("rater_id,item_id,final_score_0_5\nT01,W01a,0\n")
            raw_file = raw_dir / "Example_Rater__warmup_T01.csv"
            raw_bytes = b"rater_name,rater_id,item_id,final_score_0_5\nExample Rater,T01,W01a,N/A\n"
            raw_file.write_bytes(raw_bytes)
            identities = root / "RATER_IDENTITIES.json"
            identities.write_text(json.dumps({"T01": {"rater_name": "Example Rater", "filename_stem": "Example_Rater"}}))
            argv = ["refresh_named_ratings.py", "--input-dir", str(inputs), "--identities", str(identities)]
            with patch.object(MODULE, "EXPERIMENT", root), patch.object(sys, "argv", argv), contextlib.redirect_stdout(io.StringIO()):
                MODULE.main()
            self.assertTrue((raw_dir / "analysis/Example_Rater__warmup_T01.csv").exists())
            self.assertTrue((raw_dir / "analysis/NAMED_EXPORT_MANIFEST.json").exists())
            self.assertEqual(raw_file.read_bytes(), raw_bytes)
            alias = root / "raw_alias"
            alias.symlink_to(raw_dir, target_is_directory=True)
            for destination in (raw_dir, alias):
                with patch.object(MODULE, "EXPERIMENT", root), patch.object(sys, "argv", [*argv, "--out-dir", str(destination)]), contextlib.redirect_stderr(io.StringIO()):
                    with self.assertRaises(SystemExit):
                        MODULE.main()
                self.assertEqual(raw_file.read_bytes(), raw_bytes)

    def test_preserves_values_and_is_repeatable(self):
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "setN_A1.csv"
            original = b'rater_id,item_id,final_score_0_5,problem_note\nA1,agent_file01,0,"note, with comma"\nA1,agent_file02,,unfinished\n'
            source.write_bytes(original)
            identities = {"A1": {"rater_name": "Example Rater", "filename_stem": "Example_Rater"}}
            first = MODULE.named_export(source, identities)
            self.assertEqual(first, MODULE.named_export(source, identities))
            self.assertEqual(source.read_bytes(), original)
            name, data, receipt = first
            self.assertEqual(name, "Example_Rater__setN_A1.csv")
            rows = list(csv.DictReader(io.StringIO(data.decode())))
            self.assertEqual(rows[0]["final_score_0_5"], "0")
            self.assertEqual(rows[1]["final_score_0_5"], "")
            self.assertEqual(rows[0]["problem_note"], "note, with comma")
            self.assertEqual(list(rows[0])[0], "rater_name")
            self.assertEqual(receipt["rows"], 2)

    def test_rejects_missing_name_wrong_rater_and_duplicate_item(self):
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "setN_A1.csv"
            identities = {"A1": {"rater_name": "Example Rater", "filename_stem": "Example_Rater"}}
            for content, mapping in [
                ("A1,x,4\n", {}),
                ("T01,x,4\n", identities),
                ("A1,x,4\nA1,x,5\n", identities),
            ]:
                source.write_text("rater_id,item_id,final_score_0_5\n" + content)
                with self.assertRaises(ValueError):
                    MODULE.named_export(source, mapping)


if __name__ == "__main__":
    unittest.main()
