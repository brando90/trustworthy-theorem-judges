"""Every rating CSV export carries a source_label naming its round; nothing else about the rows changes."""
import csv
import hashlib
import importlib.util
import io
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

EXP = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("source_label", EXP / "support/scripts/source_label.py")
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class SourceLabelTests(unittest.TestCase):
    def test_every_export_row_carries_its_round(self):
        files = MODULE.export_files()
        self.assertGreaterEqual(len(files), 48)
        self.assertEqual(MODULE.check(), [])
        for path in files:
            rows = MODULE.read_rows(path)
            self.assertEqual(rows[0][-1], "source_label", path.name)
            self.assertEqual({r[-1] for r in rows[1:]}, {MODULE.label_for_filename(path.name)}, path.name)
            self.assertTrue({r[-1] for r in rows[1:]} <= set(MODULE.LABELS), path.name)

    def test_schema_note_lists_the_allowed_values_and_the_manifest_matches_the_files(self):
        schema = json.loads((EXP / "support/RATING_FORM_SCHEMA.json").read_text())
        note = schema["export_columns"]["source_label"]
        self.assertEqual(tuple(note["allowed_values"]), MODULE.LABELS)
        self.assertNotIn("source_label", schema["columns"])  # export-only, never a Sheet column
        manifest = json.loads((EXP / "ratings/RAW_MANIFEST.json").read_text())
        for entry in manifest["files"]:
            data = (EXP / entry["path"]).read_bytes()
            self.assertEqual(hashlib.sha256(data).hexdigest(), entry["sha256"], entry["filename"])
            self.assertEqual(entry["csv_columns"], [*entry["columns"], "source_label"])
            self.assertEqual(entry["source_label"], MODULE.label_for_packet(entry["packet"]))
            rows = MODULE.read_rows(EXP / entry["path"])
            self.assertEqual(rows[0], entry["csv_columns"])
            self.assertEqual(len(rows) - 1, entry["rows"])

    def test_add_label_keeps_every_original_cell(self):
        rows = [["rater_id", "item_id", "final_score_0_5", "rationale"], ["T01", "W01a", "", "line one\nline, two"], ["T01", "W01b", "N/A", ""]]
        labeled = MODULE.add_label(rows, "warm-up")
        self.assertEqual([r[:-1] for r in labeled], rows)
        self.assertEqual([r[-1] for r in labeled], ["source_label", "warm-up", "warm-up"])
        self.assertIs(MODULE.add_label(labeled, "warm-up"), labeled)  # idempotent
        with self.assertRaises(ValueError):
            MODULE.add_label(labeled, "main")  # never relabel a different round
        with self.assertRaises(ValueError):
            MODULE.add_label(rows, "june")  # only allowed values

    def test_apply_backfills_a_file_and_refreshes_its_hash(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            (root / "analysis").mkdir()
            old = b'rater_name,rater_id,item_id,final_score_0_5\nExample Rater,T01,W01a,"2"\n'
            data = io.StringIO(newline="")
            csv.writer(data, lineterminator="\n").writerows(MODULE.read_rows_from(old))
            raw = data.getvalue().encode()
            (root / "Example_Rater__warmup_T01.csv").write_bytes(raw)
            old_hash = hashlib.sha256(raw).hexdigest()
            (root / "RAW_MANIFEST.json").write_text(json.dumps({"files": [{
                "filename": "Example_Rater__warmup_T01.csv", "packet": "warmup", "columns": ["rater_name", "rater_id", "item_id", "final_score_0_5"],
                "sha256": old_hash}]}))
            (root / "SUMMARY.json").write_text(json.dumps({"sheets": [{"csv_sha256": old_hash}]}))
            (root / "analysis/NAMED_EXPORT_MANIFEST.json").write_text(json.dumps({"collected_files": []}))
            with patch.object(MODULE, "RATINGS", root), patch.object(MODULE, "MANIFESTS", (
                    root / "RAW_MANIFEST.json", root / "SUMMARY.json", root / "analysis/NAMED_EXPORT_MANIFEST.json")):
                with patch("builtins.print"):
                    MODULE.apply()
                self.assertEqual(MODULE.check(), [])
                new = (root / "Example_Rater__warmup_T01.csv").read_bytes()
                self.assertEqual(new.decode(), "rater_name,rater_id,item_id,final_score_0_5,source_label\nExample Rater,T01,W01a,2,warm-up\n")
                manifest = json.loads((root / "RAW_MANIFEST.json").read_text())
                self.assertEqual(manifest["files"][0]["sha256"], hashlib.sha256(new).hexdigest())
                self.assertEqual(json.loads((root / "SUMMARY.json").read_text())["sheets"][0]["csv_sha256"], hashlib.sha256(new).hexdigest())


if __name__ == "__main__":
    unittest.main()
