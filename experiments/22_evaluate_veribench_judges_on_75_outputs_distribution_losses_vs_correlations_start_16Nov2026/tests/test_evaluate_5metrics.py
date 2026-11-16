#!/usr/bin/env python3
"""Unit and synthetic-control tests for evaluate_5metrics.py."""
from __future__ import annotations

import csv
import json
import math
import sys
import tempfile
import unittest
from pathlib import Path

import numpy as np

EXP_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(EXP_DIR / "scripts"))

import evaluate_5metrics as ev  # noqa: E402


class TestEvaluate5Metrics(unittest.TestCase):
    def test_point_mass_controls(self) -> None:
        # Control 1: point mass on observed rating 4 -> RPS=0, CE=0, TVD=0, MAE=0, bias=0
        P = np.array([[0.0, 0.0, 0.0, 0.0, 1.0, 0.0]])
        Q = np.array([[0.0, 0.0, 0.0, 0.0, 1.0, 0.0]])
        rps, cdf_sq, dis = ev.rps_components(P, Q)
        self.assertAlmostEqual(float(rps[0]), 0.0, places=14)
        self.assertAlmostEqual(float(cdf_sq[0]), 0.0, places=14)
        self.assertAlmostEqual(float(dis[0]), 0.0, places=14)
        self.assertAlmostEqual(float(ev.ce_per_artifact(P, Q)[0]), 0.0, places=14)
        self.assertAlmostEqual(float(ev.tvd_per_artifact(P, Q)[0]), 0.0, places=14)

        # Control 2: point mass at 0 when human rating is 5 -> RPS=1, TVD=1, CE=+inf, bias=-1
        P5 = np.array([[0.0, 0.0, 0.0, 0.0, 0.0, 1.0]])
        Q0 = np.array([[1.0, 0.0, 0.0, 0.0, 0.0, 0.0]])
        rps5, _, _ = ev.rps_components(P5, Q0)
        self.assertAlmostEqual(float(rps5[0]), 1.0, places=14)
        self.assertAlmostEqual(float(ev.tvd_per_artifact(P5, Q0)[0]), 1.0, places=14)
        self.assertTrue(math.isinf(float(ev.ce_per_artifact(P5, Q0)[0])))
        panel = ev.compute_panel(P5, Q0)
        self.assertAlmostEqual(panel["mae_0_1"], 1.0, places=14)
        self.assertAlmostEqual(panel["signed_bias_0_1"], -1.0, places=14)

    def test_split_disagreement_and_correlation_blindness(self) -> None:
        # Control 3: half mass at 0 and 5, human observations 0 and 5 -> RPS=0.25, TVD=0, CE=ln(2)
        P_05 = np.array([[0.5, 0.0, 0.0, 0.0, 0.0, 0.5]])
        rps, cdf_sq, dis = ev.rps_components(P_05, P_05)
        self.assertAlmostEqual(float(cdf_sq[0]), 0.0, places=14)
        self.assertAlmostEqual(float(dis[0]), 0.25, places=14)
        self.assertAlmostEqual(float(rps[0]), 0.25, places=14)
        self.assertAlmostEqual(float(ev.tvd_per_artifact(P_05, P_05)[0]), 0.0, places=14)
        self.assertAlmostEqual(float(ev.ce_per_artifact(P_05, P_05)[0]), math.log(2.0), places=14)

        # Control 4: raters split evenly between 3 and 5 (mean=4).
        # Judge A predicts 50/50 on 3 and 5; Judge B puts all mass on 4.
        # Both have expected rating 4 (0.8 on [0,1]), so correlation cannot tell them apart,
        # while RPS is 0.10 for Judge A vs 0.20 for Judge B.
        P_35 = np.array([[0.0, 0.0, 0.0, 0.5, 0.0, 0.5]])
        Q_A = np.array([[0.0, 0.0, 0.0, 0.5, 0.0, 0.5]])
        Q_B = np.array([[0.0, 0.0, 0.0, 0.0, 1.0, 0.0]])
        self.assertAlmostEqual(float((Q_A @ ev.GRID)[0]), float((Q_B @ ev.GRID)[0]), places=14)
        self.assertAlmostEqual(float(ev.rps_components(P_35, Q_A)[0][0]), 0.10, places=14)
        self.assertAlmostEqual(float(ev.rps_components(P_35, Q_B)[0][0]), 0.20, places=14)

    def test_equal_artifact_weighting_and_mse_decomposition(self) -> None:
        # Artifact 1: 1 rating (r=4), zero loss. Artifact 2: 3 ratings (all r=5), worst loss (pred=0).
        P = np.array([[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], dtype=float)
        Q = np.array([[0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 0, 0]], dtype=float)
        panel = ev.compute_panel(P, Q)
        self.assertAlmostEqual(panel["rps"], 0.5, places=14)
        self.assertAlmostEqual(panel["tvd"], 0.5, places=14)

        # Exact Pearson MSE decomposition check on random nonconstant vectors
        rng = np.random.default_rng(123)
        x = rng.uniform(0.1, 0.9, size=25)
        y = rng.uniform(0.1, 0.9, size=25)
        decomp = ev.mse_decomposition(x, y)
        reconstructed = decomp["bias_sq_0_1"] + decomp["scale_mismatch_sq_0_1"] + decomp["ordering_imperfection_0_1"]
        self.assertAlmostEqual(decomp["mse_0_1"], reconstructed, places=13)

    def test_privacy_guard_blocks_forbidden_keys(self) -> None:
        with self.assertRaises(AssertionError):
            ev.assert_no_private_ratings({"nested": {"ratings": [1, 2, 3]}})
        with self.assertRaises(AssertionError):
            ev.assert_no_private_ratings({"scores": list(range(30))})
        ev.assert_no_private_ratings({"ok": {"rps": 0.14, "weights": [0.2, 0.8]}})
        cleaned = ev._clean_dict({"flag": True, "zero": False, "n": np.int64(3)})
        self.assertIs(cleaned["flag"], True)
        self.assertIs(cleaned["zero"], False)
        self.assertEqual(cleaned["n"], 3)

    def test_score_forecasts_cli_on_exp09_csv(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tdir = Path(tmp)
            csv1 = tdir / "Rater_A__native_main_A1.csv"
            csv2 = tdir / "Rater_B__native_main_T01.csv"
            header = [
                "rater_name",
                "rater_id",
                "item_id",
                "task_folder",
                "candidate_file",
                "final_score_0_5",
                "ai_assisted_rating_attestation",
                "minutes_spent",
                "confidence",
                "rationale",
                "problem_note",
            ]
            rows1 = [
                ["Brando Miranda", "A1", "item_01", "task_01", "a1.lean", "5", "yes", "5", "high", "ok", ""],
                ["Brando Miranda", "A1", "item_02", "task_01", "a2.lean", "3", "yes", "5", "medium", "ok", ""],
                ["Brando Miranda", "A1", "item_03", "task_02", "a3.lean", "1", "yes", "5", "high", "ok", ""],
                ["Brando Miranda", "A1", "item_04", "task_03", "a4.lean", "", "", "", "", "", ""],
            ]
            rows2 = [
                ["Sri", "T05", "item_01", "task_01", "a1.lean", "5", "yes", "6", "high", "ok", ""],
                ["Sri", "T05", "item_02", "task_01", "a2.lean", "5", "yes", "6", "high", "ok", ""],
                ["Sri", "T05", "item_03", "task_02", "a3.lean", "1", "yes", "6", "high", "ok", ""],
            ]
            for p, rws in [(csv1, rows1), (csv2, rows2)]:
                with p.open("w", newline="") as fh:
                    w = csv.writer(fh)
                    w.writerow(header)
                    w.writerows(rws)
            fjson = tdir / "forecasts.json"
            fjson.write_text(
                json.dumps(
                    {
                        "item_01": [0.01, 0.01, 0.01, 0.02, 0.05, 0.90],
                        "item_02": [0.01, 0.01, 0.02, 0.48, 0.00, 0.48],
                        "item_03": [0.05, 0.85, 0.05, 0.02, 0.02, 0.01],
                    }
                )
            )
            out_json = tdir / "out.json"
            args = ev.build_parser().parse_args(
                [
                    "score-forecasts",
                    "--ratings-csv",
                    str(csv1),
                    str(csv2),
                    "--forecasts-json",
                    str(fjson),
                    "--bootstrap",
                    "200",
                    "--out",
                    str(out_json),
                ]
            )
            res = ev.score_forecasts_cli(args)
            self.assertEqual(res["n_rated_items"], 3)
            self.assertEqual(res["n_scored_items"], 3)
            self.assertEqual(res["n_ratings_scored"], 6)
            self.assertEqual(res["n_tasks_scored"], 2)
            self.assertEqual(res["n_unscored_csv_rows"], 1)
            self.assertTrue(out_json.is_file())
            ev.assert_no_private_ratings(json.loads(out_json.read_text()))


if __name__ == "__main__":
    unittest.main()
