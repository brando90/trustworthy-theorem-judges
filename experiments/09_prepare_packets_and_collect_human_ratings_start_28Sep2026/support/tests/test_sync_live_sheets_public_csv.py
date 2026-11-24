"""Tests for fail-closed public CSV Google Sheets sync."""
from __future__ import annotations

import csv
import hashlib
import importlib.util
import io
import json
import tempfile
import unittest
from pathlib import Path

EXP = Path(__file__).resolve().parents[2]
SCRIPT_PATH = EXP / "support/scripts/sync_live_sheets_public_csv.py"
SPEC = importlib.util.spec_from_file_location("sync_live_sheets_public_csv", SCRIPT_PATH)
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def make_fixture(root: Path) -> tuple[list[str], dict]:
    schema = json.loads((EXP / "support/RATING_FORM_SCHEMA.json").read_text())
    cols = schema["main_form_v7_columns"]
    (root / "support/scripts").mkdir(parents=True)
    (root / "ratings").mkdir(parents=True)
    (root / "support/RATING_FORM_SCHEMA.json").write_text(json.dumps(schema))

    def dump_rows(rows: list[list[str]]) -> bytes:
        buf = io.StringIO(newline="")
        csv.writer(buf, lineterminator="\n").writerows(rows)
        return buf.getvalue().encode()

    a1_bytes = dump_rows([
        cols + ["source_label"],
        ["Brando Miranda", "A1", "item1", "task_01", "agent_1.lean"] + [""] * 10 + ["main"],
    ])
    (root / "ratings/Brando_Miranda__native_main_A1.csv").write_bytes(a1_bytes)

    t05_bytes = dump_rows([
        cols + ["source_label"],
        ["Sri", "T05", "item2", "task_02", "agent_2.lean"] + [""] * 10 + ["main"],
        ["Sri", "T05", "item1", "task_01", "agent_1.lean"] + [""] * 10 + ["main"],
    ])
    (root / "ratings/Sri__native_main_T05.csv").write_bytes(t05_bytes)

    t25_bytes = dump_rows([
        cols + ["source_label"],
        ["John", "T25", "item2", "task_02", "agent_2.lean"] + [""] * 10 + ["main"],
        ["John", "T25", "item1", "task_01", "agent_1.lean"] + [""] * 10 + ["main"],
    ])
    (root / "ratings/John__native_main_T25.csv").write_bytes(t25_bytes)

    t06_bytes = dump_rows([
        cols + ["source_label"],
        ["Donald", "T06", "item1", "task_01", "agent_1.lean"] + [""] * 10 + ["main"],
        ["Donald", "T06", "item20", "task_16", "task_16/agent_2.lean"] + [""] * 10 + ["main"],
    ])
    (root / "ratings/Donald__native_main_T06.csv").write_bytes(t06_bytes)

    manifest = {
        "checked_date": "11-18-2026",
        "recorded_utc": "old",
        "numeric_observations": 15,
        "not_applicable_rows": 3,
        "files": [
            {"rater_name": "Warmup", "rater_id": "T01", "packet": "warmup", "numeric_ratings": 15, "not_applicable_rows": 3},
            {
                "rater_name": "Brando Miranda",
                "rater_id": "A1",
                "packet": "native_main",
                "filename": "Brando_Miranda__native_main_A1.csv",
                "spreadsheet_id": "sid_a1",
                "path": "ratings/Brando_Miranda__native_main_A1.csv",
                "columns": cols,
                "csv_columns": [*cols, "source_label"],
                "source_label": "main",
                "sha256": hashlib.sha256(a1_bytes).hexdigest(),
                "numeric_ratings": 0,
                "not_applicable_rows": 0,
            },
            {
                "rater_name": "Sri",
                "rater_id": "T05",
                "packet": "native_main",
                "filename": "Sri__native_main_T05.csv",
                "spreadsheet_id": "sid_t05",
                "path": "ratings/Sri__native_main_T05.csv",
                "columns": cols,
                "csv_columns": [*cols, "source_label"],
                "source_label": "main",
                "sha256": hashlib.sha256(t05_bytes).hexdigest(),
                "numeric_ratings": 0,
                "not_applicable_rows": 0,
            },
            {
                "rater_name": "John",
                "rater_id": "T25",
                "packet": "native_main",
                "filename": "John__native_main_T25.csv",
                "spreadsheet_id": "sid_t25",
                "path": "ratings/John__native_main_T25.csv",
                "columns": cols,
                "csv_columns": [*cols, "source_label"],
                "source_label": "main",
                "sha256": hashlib.sha256(t25_bytes).hexdigest(),
                "numeric_ratings": 0,
                "not_applicable_rows": 0,
            },
            {
                "rater_name": "Donald",
                "rater_id": "T06",
                "packet": "native_main",
                "filename": "Donald__native_main_T06.csv",
                "spreadsheet_id": "sid_t06",
                "path": "ratings/Donald__native_main_T06.csv",
                "columns": cols,
                "csv_columns": [*cols, "source_label"],
                "source_label": "main",
                "sha256": hashlib.sha256(t06_bytes).hexdigest(),
                "numeric_ratings": 0,
                "not_applicable_rows": 0,
            },
        ],
        "full_team_100_native_revision": {"date": "11-18-2026", "main_numeric_observations": 0},
    }
    (root / "ratings/RAW_MANIFEST.json").write_text(json.dumps(manifest))
    (root / "ratings/SUMMARY.json").write_text(json.dumps({"checked_date": "11-18-2026", "full_team_100_native_sync": {}}))
    (root / "README.md").write_text(
        "<!-- grading-status:start -->\n"
        "Live progress read from the 4 Sheets on 11-18-2026 at 20:42 PST; Total scored: **0** of 400.\n"
        "| ID | Rater | Email | Role | Warm-up | Packet email | Scored | Links |\n"
        "| `A1` | Brando Miranda | a | Author | 0/6 | sent | **0/1** | l |\n"
        "| `T05` | Sri | b | Author | 6/6 | sent | **0/2** | l |\n"
        "| `T25` | John | c | Author | none | sent | **0/2** | l |\n"
        "| `T06` | Donald | d | Author | 0/6 | sent | **0/2** | l |\n"
        "<!-- grading-status:end -->\n"
        "**Also rating: `T30` Max Sieb** (x), 0/100 scored on 11-18-2026; Rater data policy (details).\n"
    )
    (root / "ratings/README.md").write_text(
        "All **33** current main Google Sheets (desc) have **100** rows (0/100 completed)\n"
        "**Checked: 11-16-2026.** old text\n"
        "| `A1` | Brando | c | s | 0/100 (note) |\n"
        "| `T05` | Sri | c | s | 0/100 (note) |\n"
        "| `T25` | John | c | s | 0/100 (note) |\n"
        "| `T06` | Donald | c | s | 0/100 (note) |\n"
    )
    return cols, manifest


def live_fixture_tables(root: Path, manifest: dict) -> dict[str, list[list[str]]]:
    return {
        entry["spreadsheet_id"]: [row[:-1] for row in MOD.read_rows_from((root / entry["path"]).read_bytes())]
        for entry in manifest["files"] if entry.get("packet") == "native_main"
    }


class SyncLiveSheetsTests(unittest.TestCase):
    def test_sync_reordered_sheets_attestations_and_allowlisted_anomaly(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            cols, _ = make_fixture(root)

            def fake_fetch(sid: str):
                if sid == "sid_a1":
                    return [cols, ["Brando Miranda", "A1", "item1", "task_01", "agent_1.lean"]]
                if sid == "sid_t05":
                    # Reordered + mixed attestation/N/A
                    return [
                        cols,
                        ["Sri", "T05", "item1", "task_01", "agent_1.lean", "Y", "Y", "N", "none", "5", "yes", "4", "high", "", "good"],
                        ["Sri", "T05", "item2", "task_02", "agent_2.lean", "N", "N", "N", "none", "N/A", "partial", "3", "low", "ref", ""],
                    ]
                if sid == "sid_t25":
                    # Reordered blank sheet
                    return [
                        cols,
                        ["John", "T25", "item1", "task_01", "agent_1.lean"],
                        ["John", "T25", "item2", "task_02", "agent_2.lean"],
                    ]
                return [
                    cols,
                    ["Donald", "T06", "item1", "task_01", "agent_1.lean", "Y", "Y", "N", "none", "5", "", "", "high", "", ""],
                    ["Donald", "T06", "item20", "task_16", "this one has borderline spam.", "Y", "Y", "N", "none", "5", "yes", "", "medium", "", ""],
                ]

            backup = root / "support/sheet_exports/11-24-2026_before_first_ratings_sync"
            res = MOD.run_sync(
                dry_run=False,
                fetcher=fake_fetch,
                experiment_dir=root,
                backup_dir=backup,
                known_candidate_anomalies={("T06", "item20"): "this one has borderline spam."},
            )
            self.assertEqual(res["main_numeric_observations"], 3)
            self.assertEqual(res["main_not_applicable_rows"], 1)
            self.assertEqual(res["reordered_by_rater"], ["T05", "T25"])
            self.assertEqual(res["attestation_breakdown_when_scored"], {"": 1, "partial": 1, "yes": 2})
            self.assertEqual(len(res["identity_cell_anomalies"]), 1)
            self.assertEqual(set(res["changed_files"]), {"Sri__native_main_T05.csv", "John__native_main_T25.csv", "Donald__native_main_T06.csv"})
            self.assertTrue((backup / "MANIFEST.json").exists())

            with (root / "ratings/Donald__native_main_T06.csv").open(newline="") as fh:
                t06_csv = list(csv.DictReader(fh))
            self.assertEqual(t06_csv[1]["candidate_file"], "this one has borderline spam.")
            self.assertEqual(t06_csv[0]["ai_assisted_rating_attestation (AI help is allowed)"], "")

            with (root / "ratings/Sri__native_main_T05.csv").open(newline="") as fh:
                t05_csv = list(csv.DictReader(fh))
            self.assertEqual([r["item_id"] for r in t05_csv], ["item1", "item2"])
            self.assertEqual(t05_csv[0]["final_score_0_5"], "5")
            self.assertEqual(t05_csv[1]["final_score_0_5"], "N/A")

            manifest = json.loads((root / "ratings/RAW_MANIFEST.json").read_text())
            self.assertEqual(manifest["numeric_observations"], 18)
            self.assertEqual(manifest["not_applicable_rows"], 4)
            readme = (root / "README.md").read_text()
            self.assertIn("**2/2**", readme)
            self.assertIn("unverified", readme)
            self.assertIn("Coordinator check", readme)

    def test_later_score_revisions_keep_each_prior_raw_snapshot(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            cols, manifest = make_fixture(root)
            tables = live_fixture_tables(root, manifest)
            backup = root / "support/sheet_exports/revisions"
            score_idx = cols.index("final_score_0_5")
            tables["sid_t05"][1][score_idx] = "5"
            MOD.run_sync(fetcher=tables.__getitem__, experiment_dir=root, backup_dir=backup)
            previous = (root / "ratings/Sri__native_main_T05.csv").read_bytes()
            first_receipt = (backup / "MANIFEST.json").read_bytes()
            tables["sid_t05"][1][score_idx] = "4"
            MOD.run_sync(fetcher=tables.__getitem__, experiment_dir=root, backup_dir=backup)
            self.assertEqual((backup / "MANIFEST.json").read_bytes(), first_receipt)
            revisions = list(backup.glob("*_revision_*/MANIFEST.json"))
            self.assertEqual(len(revisions), 1)
            receipt = json.loads(revisions[0].read_text())
            self.assertFalse(receipt["zero_observations_overwritten"])
            self.assertEqual((revisions[0].parent / receipt["files"][0]["archived_snapshot"]).read_bytes(), previous)
            self.assertIn("Rater data policy (details).", (root / "README.md").read_text())

    def test_cleared_responses_are_preserved_as_blank_with_revision_history(self):
        for reordered in (False, True):
            with self.subTest(reordered=reordered), tempfile.TemporaryDirectory() as td:
                root = Path(td)
                cols, manifest = make_fixture(root)
                tables = live_fixture_tables(root, manifest)
                backup = root / "backup"
                tables["sid_t05"][1][cols.index("final_score_0_5")] = "0"
                MOD.run_sync(fetcher=tables.__getitem__, experiment_dir=root, backup_dir=backup)
                scored_bytes = (root / "ratings/Sri__native_main_T05.csv").read_bytes()
                tables["sid_t05"][1][cols.index("final_score_0_5")] = ""
                if reordered:
                    tables["sid_t05"] = [cols, *reversed(tables["sid_t05"][1:])]
                result = MOD.run_sync(fetcher=tables.__getitem__, experiment_dir=root, backup_dir=backup)
                self.assertEqual(result["main_numeric_observations"], 0)
                saved = MOD.read_rows_from((root / "ratings/Sri__native_main_T05.csv").read_bytes())
                self.assertEqual([row[:-1] for row in saved], tables["sid_t05"])
                archive = next(backup.glob("*_revision_*/Sri__native_main_T05_before_sync.csv"))
                self.assertEqual(archive.read_bytes(), scored_bytes)

    def test_invalid_readme_aborts_before_any_raw_or_manifest_writes(self):
        for broken_target in ("README.md", "ratings/README.md"):
            with self.subTest(target=broken_target), tempfile.TemporaryDirectory() as td:
                root = Path(td)
                cols, manifest = make_fixture(root)
                tables = live_fixture_tables(root, manifest)
                tables["sid_t05"][1][cols.index("final_score_0_5")] = "5"
                (root / broken_target).write_text("missing status table")
                before = {path: path.read_bytes() for path in root.rglob("*") if path.is_file()}
                backup = root / "support/sheet_exports/revisions"
                with self.assertRaisesRegex(ValueError, "README"):
                    MOD.run_sync(fetcher=tables.__getitem__, experiment_dir=root, backup_dir=backup)
                self.assertEqual({path: path.read_bytes() for path in root.rglob("*") if path.is_file()}, before)
                self.assertFalse(backup.exists())

    def test_local_raw_manifest_mismatch_aborts_before_fetch_or_write(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            make_fixture(root)
            path = root / "ratings/Brando_Miranda__native_main_A1.csv"
            path.write_bytes(path.read_bytes() + b"\n")
            def unexpected_fetch(_):
                self.fail("Manifest mismatch must fail before fetching")
            with self.assertRaisesRegex(ValueError, "pre-sync CSV does not match"):
                MOD.run_sync(fetcher=unexpected_fetch, experiment_dir=root, backup_dir=root / "backup")

    def test_existing_inline_coordinator_note_retains_data_policy_on_refresh(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            cols, manifest = make_fixture(root)
            tables = live_fixture_tables(root, manifest)
            tables["sid_t05"][1][cols.index("final_score_0_5")] = "5"
            path = root / "README.md"
            path.write_text(path.read_text().replace("Rater data policy (", "<!-- coordinator_sync_flags --> old flags. Rater data policy ("))
            MOD.run_sync(fetcher=tables.__getitem__, experiment_dir=root, backup_dir=root / "backup")
            self.assertIn("Rater data policy (details).", path.read_text())
            self.assertIn("\n<!-- grading-status:end -->", path.read_text())

    def test_rejects_bad_score_header_identity_or_uninspected_candidate_edit(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            cols, _ = make_fixture(root)
            old_bytes = (root / "ratings/Brando_Miranda__native_main_A1.csv").read_bytes()

            bad_header = [["wrong", *cols[1:]], ["Brando Miranda", "A1", "item1", "task_01", "agent_1.lean"]]
            with self.assertRaisesRegex(ValueError, "unexpected header"):
                MOD.validate_and_normalize_table(bad_header, cols, old_bytes, "A1")

            bad_id = [cols, ["Brando Miranda", "A1", "WRONG_ITEM", "task_01", "agent_1.lean"]]
            with self.assertRaisesRegex(ValueError, "unknown item_id"):
                MOD.validate_and_normalize_table(bad_id, cols, old_bytes, "A1")

            bad_cand = [cols, ["Brando Miranda", "A1", "item1", "task_01", "oops.lean"]]
            with self.assertRaisesRegex(ValueError, "uninspected candidate_file edit"):
                MOD.validate_and_normalize_table(bad_cand, cols, old_bytes, "A1")

            bad_score = [cols, ["Brando Miranda", "A1", "item1", "task_01", "agent_1.lean", "", "", "", "", "7"]]
            with self.assertRaisesRegex(ValueError, "invalid final_score_0_5"):
                MOD.validate_and_normalize_table(bad_score, cols, old_bytes, "A1")

    def test_known_candidate_cell_does_not_allow_unreviewed_new_text(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            cols, _ = make_fixture(root)
            old = (root / "ratings/Donald__native_main_T06.csv").read_bytes()
            table = [row[:-1] for row in MOD.read_rows_from(old)]
            table[2][4] = "different new candidate edit"
            with self.assertRaisesRegex(ValueError, "uninspected candidate_file edit"):
                MOD.validate_and_normalize_table(
                    table, cols, old, "T06",
                    known_candidate_anomalies={("T06", "item20"): "this one has borderline spam."},
                )

    def test_attestation_summary_text_includes_all_categories_and_case_variants(self):
        text = MOD._attestation_summary_text({
            "T01": {"attestation_breakdown_when_scored": {"yes": 1, "Yes": 1, "no": 1}},
            "T02": {"attestation_breakdown_when_scored": {"unsure": 1, "partial": 1, "": 1}},
        })
        self.assertEqual(
            text,
            "2 `yes`, 1 `no`, 1 `unsure`, 1 `partial` (non-dropdown free text), 1 blank across 6 scored rows",
        )

    def test_second_idempotent_sync_preserves_anomaly_and_backup_and_dry_run_is_readonly(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            cols, manifest = make_fixture(root)
            # Include item20 in A1 so canonical_candidates covers the T06 anomaly across repeated syncs.
            buf = io.StringIO(newline="")
            csv.writer(buf, lineterminator="\n").writerows([
                cols + ["source_label"],
                ["Brando Miranda", "A1", "item1", "task_01", "agent_1.lean"] + [""] * 10 + ["main"],
                ["Brando Miranda", "A1", "item20", "task_16", "task_16/agent_2.lean"] + [""] * 10 + ["main"],
            ])
            a1_bytes = buf.getvalue().encode()
            (root / "ratings/Brando_Miranda__native_main_A1.csv").write_bytes(a1_bytes)
            manifest["files"][1]["sha256"] = hashlib.sha256(a1_bytes).hexdigest()
            manifest["files"][1]["assigned_rows"] = 2
            manifest["files"][1]["rows"] = 2
            (root / "ratings/RAW_MANIFEST.json").write_text(json.dumps(manifest))

            def fake_fetch(sid: str):
                if sid == "sid_a1":
                    return [
                        cols,
                        ["Brando Miranda", "A1", "item1", "task_01", "agent_1.lean"],
                        ["Brando Miranda", "A1", "item20", "task_16", "task_16/agent_2.lean"],
                    ]
                if sid == "sid_t05":
                    return [
                        cols,
                        ["Sri", "T05", "item1", "task_01", "agent_1.lean", "Y", "Y", "N", "none", "5", "yes"],
                        ["Sri", "T05", "item2", "task_02", "agent_2.lean", "Y", "Y", "N", "none", "4", "no"],
                    ]
                if sid == "sid_t25":
                    return [
                        cols,
                        ["John", "T25", "item2", "task_02", "agent_2.lean"],
                        ["John", "T25", "item1", "task_01", "agent_1.lean"],
                    ]
                return [
                    cols,
                    ["Donald", "T06", "item1", "task_01", "agent_1.lean", "Y", "Y", "N", "none", "5", "unsure"],
                    ["Donald", "T06", "item20", "task_16", "this one has borderline spam.", "Y", "Y", "N", "none", "5", "yes"],
                ]

            backup = root / "support/sheet_exports/11-24-2026_before_first_ratings_sync"
            dry_res = MOD.run_sync(
                dry_run=True,
                fetcher=fake_fetch,
                experiment_dir=root,
                backup_dir=backup,
                known_candidate_anomalies={("T06", "item20"): "this one has borderline spam."},
            )
            self.assertTrue(dry_res["dry_run"])
            self.assertFalse(backup.exists())
            self.assertEqual(json.loads((root / "ratings/RAW_MANIFEST.json").read_text())["numeric_observations"], 15)

            res1 = MOD.run_sync(
                dry_run=False,
                fetcher=fake_fetch,
                experiment_dir=root,
                backup_dir=backup,
                known_candidate_anomalies={("T06", "item20"): "this one has borderline spam."},
            )
            self.assertEqual(len(res1["identity_cell_anomalies"]), 1)
            backup_manifest_bytes = (backup / "MANIFEST.json").read_bytes()

            res2 = MOD.run_sync(
                dry_run=False,
                fetcher=fake_fetch,
                experiment_dir=root,
                backup_dir=backup,
                known_candidate_anomalies={("T06", "item20"): "this one has borderline spam."},
            )
            self.assertEqual(res2["changed_files"], [])
            self.assertEqual(len(res2["identity_cell_anomalies"]), 1)
            self.assertEqual((backup / "MANIFEST.json").read_bytes(), backup_manifest_bytes)
            manifest_after = json.loads((root / "ratings/RAW_MANIFEST.json").read_text())
            self.assertEqual(len(manifest_after["full_team_100_native_revision"]["identity_cell_anomalies"]), 1)
            ratings_readme = (root / "ratings/README.md").read_text()
            self.assertIn("2/2", ratings_readme)
            self.assertIn("4/8", ratings_readme)

    def test_na_only_rater_and_zero_scored_anomaly_formatting(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            cols, manifest = make_fixture(root)
            tables = live_fixture_tables(root, manifest)
            tables["sid_t06"][2][4] = "this one has borderline spam."
            tables["sid_t06"][2][cols.index("problem_note")] = "note"
            tables["sid_t05"][1][cols.index("final_score_0_5")] = "N/A"
            res = MOD.run_sync(
                dry_run=False,
                fetcher=tables.__getitem__,
                experiment_dir=root,
                backup_dir=root / "backup",
                known_candidate_anomalies={("T06", "item20"): "this one has borderline spam."},
            )
            self.assertEqual(res["main_numeric_observations"], 0)
            self.assertEqual(res["main_not_applicable_rows"], 1)
            ratings_readme = (root / "ratings/README.md").read_text()
            self.assertIn("scored across 1 raters", ratings_readme)
            # Clear N/A so 0 scored rows remain with an active candidate_file anomaly
            tables["sid_t05"][1][cols.index("final_score_0_5")] = ""
            MOD.run_sync(
                dry_run=False,
                fetcher=tables.__getitem__,
                experiment_dir=root,
                backup_dir=root / "backup",
                known_candidate_anomalies={("T06", "item20"): "this one has borderline spam."},
            )
            exp_readme = (root / "README.md").read_text()
            self.assertNotIn("Attestations (`ai_assisted_rating_attestation (AI help is allowed)`): ;", exp_readme)
            self.assertIn("`T06` (`item20`) has participant text in `candidate_file`", exp_readme)


if __name__ == "__main__":
    unittest.main()
