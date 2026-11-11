"""Synthetic checks for name enrichment without changing or duplicating ratings."""
import csv
import importlib.util
import io
from pathlib import Path
import tempfile
import unittest

PATH = Path(__file__).resolve().parents[1] / "scripts/refresh_named_ratings.py"
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

    def test_timing_estimates_preserve_raw_data_and_enforce_total(self):
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "warmup_T01.csv"
            original = b"rater_id,item_id,final_score_0_5,minutes_spent\nT01,W01a,0,\nT01,W01b,2,\n"
            source.write_bytes(original)
            identities = {"T01": {"rater_name": "Example Rater", "filename_stem": "Example_Rater"}}
            timing = {source.name: {"reported_total_minutes": 60, "items": {
                "W01a": {"minutes": 35, "basis": "Initial familiarization"},
                "W01b": {"minutes": 25, "basis": "Follow-up comparison"}}}}
            _, data, _ = MODULE.named_export(source, identities, timing)
            rows = list(csv.DictReader(io.StringIO(data.decode())))
            self.assertEqual(sum(int(row["minutes_spent"]) for row in rows), 60)
            self.assertTrue(all(row["minutes_spent_original"] == "" for row in rows))
            self.assertTrue(all(row["minutes_spent_source"].startswith("coordinator_estimate") for row in rows))
            self.assertEqual([row["final_score_0_5"] for row in rows], ["0", "2"])
            self.assertEqual(source.read_bytes(), original)
            timing[source.name]["reported_total_minutes"] = 59
            with self.assertRaisesRegex(ValueError, "sum"):
                MODULE.named_export(source, identities, timing)
            timing[source.name]["reported_total_minutes"] = 60
            source.write_bytes(original.replace(b"W01a,0,\n", b"W01a,0,12\n"))
            with self.assertRaisesRegex(ValueError, "nonblank"):
                MODULE.named_export(source, identities, timing)

    def test_background_annotation_does_not_rewrite_lean_self_report(self):
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "warmup_T01.csv"
            original = b"rater_id,item_id,final_score_0_5,lean_familiarity\nT01,W01a,0,none\n"
            source.write_bytes(original)
            identities = {"T01": {"rater_name": "Example Rater", "filename_stem": "Example_Rater",
                                  "programming_languages_background": "Coursework",
                                  "background_source": "Coordinator report"}}
            _, data, _ = MODULE.named_export(source, identities)
            row = next(csv.DictReader(io.StringIO(data.decode())))
            self.assertEqual(list(row)[:2], ["rater_name", "rater_id"])
            self.assertEqual(row["programming_languages_background"], "Coursework")
            self.assertEqual(row["background_source"], "Coordinator report")
            self.assertEqual(row["lean_familiarity"], "none")
            self.assertEqual(row["final_score_0_5"], "0")
            self.assertEqual(source.read_bytes(), original)

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
