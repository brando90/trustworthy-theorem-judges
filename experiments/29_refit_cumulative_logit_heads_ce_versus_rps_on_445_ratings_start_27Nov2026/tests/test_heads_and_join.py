"""Checks for the cumulative-logit head and the item_id join. CPU only."""
import csv
import json
import sys
import unittest
from pathlib import Path

import numpy as np

EXP = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(EXP / "scripts"))
from lib29 import Ordinal, ce, rps, smooth  # noqa: E402


class HeadTests(unittest.TestCase):
    def test_rps_floor_is_a_lower_bound(self):
        rng = np.random.default_rng(0)
        P = smooth(rng.random((12, 6)))
        Q = smooth(rng.random((12, 6)))
        self.assertTrue(np.all(rps(P, Q) + 1e-12 >= rps(P, P)))

    def test_ordinal_simplex_and_recovers_a_direction(self):
        rng = np.random.default_rng(1)
        n = 40
        x = rng.normal(size=n)
        # Higher x shifts probability toward 5.
        latent = 1.5 * x
        theta = np.array([-1.0, -0.2, 0.4, 1.0, 1.8])
        z = theta[None, :] - latent[:, None]
        F = 1 / (1 + np.exp(-z))
        F = np.concatenate([np.zeros((n, 1)), F, np.ones((n, 1))], 1)
        prob = np.diff(F, axis=1)
        ratings = [int(rng.choice(6, p=prob[i])) for i in range(n)]
        D = {
            "P": np.array([np.bincount([r], minlength=6) for r in ratings], float),
            "C": np.array([np.bincount([r], minlength=6) for r in ratings], float),
            "set": np.array(["old"] * n),
            "x": x,
        }
        model = Ordinal(["x"], alpha=0.1, m=0.0, objective="ce").fit(D, np.arange(n))
        Q = model.predict(D, np.arange(n))
        self.assertTrue(np.allclose(Q.sum(1), 1.0, atol=1e-8))
        self.assertTrue(np.all(Q >= -1e-12))
        # The fitted slope on x should be positive: higher x, higher expected score.
        # w is in standardized units. Sign follows the raw correlation.
        qmean = Q @ np.arange(6)
        self.assertGreater(np.corrcoef(x, qmean)[0, 1], 0.5)
        self.assertLess(ce(D["P"], Q).mean(), ce(D["P"], np.full_like(Q, 1 / 6)).mean())


class JoinTests(unittest.TestCase):
    def test_snapshot_keeps_item020_and_matches_experiment28(self):
        path = EXP / "data_11-27-2026/artifacts_11-27-2026.csv"
        audit = json.loads((EXP / "data_11-27-2026/join_audit_11-27-2026.json").read_text())
        self.assertTrue(audit["candidate_file_not_used_as_key"])
        self.assertEqual(audit["n_new_numeric_ratings"], 250)
        self.assertEqual(audit["item020_scores_via_item_id"], [5, 5, 5])
        self.assertTrue(audit["item020_histogram_unchanged_if_anomalous_row_dropped"])
        self.assertEqual(len(audit["candidate_file_anomalies"]), 1)
        with path.open(newline="") as handle:
            rows = list(csv.DictReader(handle))
        self.assertEqual(len(rows), 175)
        item = next(r for r in rows if r["item"] == "native-heavy-11-11-2026__item020")
        self.assertEqual(item["ratings_all"], "5 5 5")
        splits = {r["split"] for r in rows}
        self.assertEqual(splits, {"train", "val", "test"})
        tasks = {}
        for r in rows:
            tasks.setdefault(r["task"], set()).add(r["split"])
        self.assertTrue(all(len(v) == 1 for v in tasks.values()))


if __name__ == "__main__":
    unittest.main()
