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
