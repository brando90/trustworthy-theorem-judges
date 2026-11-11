"""Regression checks for the common form and preservation of new metadata."""
import csv
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest
from zipfile import ZipFile

EXP = Path(__file__).resolve().parents[2]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


IMPORTER = load("form_import", EXP / "scripts/legacy/import_rating_sheet.py")
REVISION = load("form_packet", EXP / "scripts/revise_rating_packet.py")


class FormRevisionTests(unittest.TestCase):
    def test_descriptive_questions_match_guide_and_validate_like_legacy(self):
        schema = json.loads((EXP / "support/RATING_FORM_SCHEMA.json").read_text())
        guide = (EXP / "rating_task_packet/RATING_FORM_GUIDE.md").read_text()
        aliases = schema["legacy_checklist_headers"]
        self.assertEqual(schema["columns"][5:9], list(aliases.values()))
        for question in aliases.values():
            self.assertIn(question, guide)
        fields = ["rater_id", "item_id", "final_score_0_5", *aliases.values()]
        for answer, invalid in [("yes", False), ("invalid", True)]:
            buf = io.StringIO()
            w = csv.writer(buf)
            w.writerow(fields)
            w.writerow(["A1", "W01a", "2", answer, "no", "yes", "handful"])
            rows, errors, _, _, _ = IMPORTER.check(buf.getvalue(), "A1", {"W01a"}, None, "warmup")
            self.assertEqual(bool(errors), invalid)
            if not invalid:
                self.assertEqual(rows[0][aliases["A"]], "y")
                self.assertEqual(rows[0][aliases["D"]], "handful")

    def test_name_first_sheet_with_shifted_comment_and_multiline_note(self):
        fields = ["rater_name", "rater_id", "item_id", "final_score_0_5", "problem_note"]
        buf = io.StringIO()
        writer = csv.writer(buf)
        writer.writerow(["", "# TLDR: existing sheet comment", "context"])
        writer.writerow(fields)
        writer.writerow(["Brando Miranda", "A1", "N01a", "0", "First line\n# literal note"])
        submitted, parsed = IMPORTER.read_rows(buf.getvalue())
        self.assertEqual(submitted, fields)
        self.assertEqual(parsed[0]["problem_note"], "First line\n# literal note")
        rows, errors, _, _, _ = IMPORTER.check(buf.getvalue(), "A1", {"N01a"}, None, "setN")
        self.assertFalse(errors)
        data = IMPORTER.normalized_csv(rows, ["rater_id", "item_id", "final_score_0_5"], submitted)
        reader = csv.DictReader(io.StringIO(data.decode()))
        self.assertEqual(reader.fieldnames[:2], ["rater_name", "rater_id"])
        row = next(reader)
        self.assertEqual(row["rater_name"], "Brando Miranda")
        self.assertEqual(row["final_score_0_5"], "0")
        self.assertEqual(row["problem_note"], "First line\n# literal note")

    def test_descriptive_background_once_or_with_legacy_labels_is_preserved(self):
        detail = "Lean tutorial; wrote 5 small proofs, about 10 hours last year."
        fields = ["rater_id", "item_id", "final_score_0_5", "lean_familiarity"]
        for later in ("", "Some"):
            buf = io.StringIO()
            w = csv.writer(buf)
            w.writerow(fields)
            w.writerow(["A1", "N01a", "2", detail])
            w.writerow(["A1", "N01b", "3", later])
            rows, errors, warnings, _, _ = IMPORTER.check(buf.getvalue(), "A1", {"N01a", "N01b"}, None, "setN")
            self.assertFalse(errors)
            self.assertEqual(rows[0]["lean_familiarity"], detail)
            self.assertEqual(rows[1]["lean_familiarity"], later.lower())
            self.assertEqual(bool(warnings), bool(later))
            data = IMPORTER.normalized_csv(rows, fields[:3], fields)
            self.assertEqual(next(csv.DictReader(io.StringIO(data.decode())))["lean_familiarity"], detail)

    def test_metadata_survives_import_and_missing_attestation_is_not_fabricated(self):
        fields = ["rater_id", "item_id", "final_score_0_5", "model_assistance", "independent_rating_attestation"]
        buf = io.StringIO()
        w = csv.writer(buf)
        w.writerow(fields)
        w.writerow(["A1", "N01a", "0", "Claude: Lean notation", ""])
        rows, errors, warnings, _, _ = IMPORTER.check(buf.getvalue(), "A1", {"N01a"}, None, "setN")
        self.assertFalse(errors)
        self.assertTrue(any("attestation" in x for x in warnings))
        encoded = IMPORTER.normalized_csv(rows, fields[:3], fields)
        result = list(csv.DictReader(io.StringIO(encoded.decode())))[0]
        self.assertEqual(result["model_assistance"], "Claude: Lean notation")
        self.assertEqual(result["independent_rating_attestation"], "")
        self.assertEqual(result["final_score_0_5"], "0")

    def test_no_attestation_is_retained_and_flagged_not_dropped(self):
        text = "rater_id,item_id,final_score_0_5,model_assistance,independent_rating_attestation\nA1,N01a,2,help,no\n"
        rows, errors, warnings, _, _ = IMPORTER.check(text, "A1", {"N01a"}, None, "setN")
        self.assertFalse(errors)
        self.assertEqual(rows[0]["independent_rating_attestation"], "no")
        self.assertTrue(any("coordinator review" in x for x in warnings))

    def test_revised_archive_preserves_scientific_bytes_and_refuses_overwrite(self):
        files = {"START_HERE.md": b"Old instructions\n", "human_judgements_prompt.md": b"Unchanged rubric\n",
                 "W01/python_source/task.py": b"# synthetic source\n",
                 "W01/gold_lean/task.lean": b"-- synthetic reference\n",
                 "W01/agent_lean/W01a.lean": b"-- synthetic candidate\n"}
        files["FILES.sha256"] = "".join(f"{hashlib.sha256(b).hexdigest()}  {n}\n" for n,b in sorted(files.items())).encode()
        with tempfile.TemporaryDirectory() as td:
            src, dst = Path(td)/"original.zip", Path(td)/"revised.zip"
            with ZipFile(src,"w") as z:
                for n,b in files.items():z.writestr("original/"+n,b)
            original = src.read_bytes()
            receipt = REVISION.revise(src,dst,"A1","https://example.invalid/sheet")
            self.assertEqual(src.read_bytes(), original)
            self.assertEqual(receipt["preserved_scientific_files"],3)
            with ZipFile(dst) as z:
                for n,b in files.items():
                    if n.endswith((".lean",".py")):
                        mapped = json.loads((EXP/"support/WARMUP_PATHS.json").read_text())["paths"].get(n, n)
                        self.assertEqual(z.read("revised/"+mapped),b)
                reader=csv.DictReader(io.StringIO(z.read("revised/ratings.csv").decode()))
                self.assertEqual(reader.fieldnames,json.loads((EXP/"support/RATING_FORM_SCHEMA.json").read_text())["columns"])
                row=next(reader)
                self.assertEqual(reader.fieldnames[:2],["rater_name","rater_id"])
                self.assertEqual(row["rater_name"],"Brando Miranda")
                self.assertEqual(row["rater_id"],"A1")
                self.assertEqual(row["item_id"],"W01a")
                self.assertEqual(row["independent_rating_attestation"],"")
            with self.assertRaises(FileExistsError):
                REVISION.revise(src,dst,"A1","https://example.invalid/sheet")
            with self.assertRaisesRegex(ValueError, "verified name"):
                REVISION.revise(src,Path(td)/"unknown.zip","UNKNOWN","https://example.invalid/sheet")


if __name__ == "__main__":
    unittest.main()
