#!/usr/bin/env python3
"""Tests for parsing integrity, loss identities, fitting and held-out bookkeeping."""
import json
import unittest
import tempfile
import time
from pathlib import Path
from unittest.mock import patch
import numpy as np
import forecast
from forecast import parse_prediction, sha, encoded
from analyze_forecasts import metrics, fit_mapping, map_probs, get_data, losses


class ForecastTests(unittest.TestCase):
    def test_strict_probability_and_abstention(self):
        self.assertEqual(parse_prediction('{"status":"forecast","probability":0.25,"reason":"x"}')["probability"], .25)
        self.assertEqual(parse_prediction('{"status":"abstain","probability":null,"reason":"x"}')["status"], "abstain")
        bad = ['{"status":"forecast","probability":true,"reason":"x"}',
               '{"status":"forecast","probability":NaN,"reason":"x"}',
               '{"status":"forecast","probability":1.1,"reason":"x"}',
               '{"status":"forecast","probability":null,"reason":"x"}',
               '{"status":"forecast","probability":0.5,"probability":0.2,"reason":"x"}',
               '```json\n{"status":"forecast","probability":0.5,"reason":"x"}\n```',
               '{"status":"abstain","probability":0.5,"reason":"x"}']
        for s in bad:
            with self.subTest(s=s), self.assertRaises(ValueError):
                parse_prediction(s)

    def test_oracle_and_constant_metrics(self):
        y = np.array([0., 1., 0., 1.])
        oracle = metrics(y, y)
        self.assertEqual(oracle["brier"], 0)
        self.assertEqual(oracle["auroc"], 1)
        self.assertAlmostEqual(oracle["pearson"], 1)
        self.assertAlmostEqual(oracle["log_loss"], -np.log(1-1e-6))
        baseline = metrics(y, np.full(4, .5))
        self.assertEqual(baseline["brier"], .25)
        self.assertAlmostEqual(baseline["log_loss"], np.log(2))
        self.assertEqual(baseline["mean_absolute_error"], .5)
        self.assertEqual(baseline["bias"], 0)
        self.assertIsNone(baseline["pearson"])
        self.assertEqual(baseline["auroc"], .5)

    def test_mapping_and_missingness(self):
        p = np.array([.3, .4, .6, .7]); y = np.array([0., 0., 1., 1.])
        for loss in ("ce", "brier"):
            fitted = fit_mapping(p, y, loss, .01)
            self.assertEqual(fitted["status"], "fit")
            self.assertGreaterEqual(fitted["b"], 0)
            mapped = map_probs(p, np.zeros(4, dtype=bool), fitted)
            self.assertTrue(np.all(np.diff(mapped) >= 0))
            self.assertLess(metrics(y, mapped)["brier"], metrics(y, p)["brier"])
            missing = np.array([False, True, False, False])
            self.assertEqual(map_probs(p, missing, fitted)[1], .5)

    def test_split_and_failure_denominator(self):
        labels = [{"id":"a", "family":"A", "split":"train", "label":0},
                  {"id":"b", "family":"B", "split":"test", "label":1},
                  {"id":"c", "family":"B", "split":"test", "label":0},
                  {"id":"d", "family":"B", "split":"test", "label":None}]
        receipts = {"a":{"status":"forecast", "probability":.2}, "b":{"status":"invalid_response"},
                    "c":{"status":"abstain"}, "d":{"status":"abstain"}}
        selected, y, p, missing, families = get_data(labels, receipts, "test")
        self.assertEqual([r["id"] for r in selected], ["b", "c"])
        self.assertEqual(len(y), 2)
        np.testing.assert_array_equal(p, [.5, .5])
        self.assertTrue(missing.all())
        self.assertEqual(set(families), {"B"})

    def test_request_hash_depends_on_input(self):
        self.assertNotEqual(sha(encoded({"statement":"a"})), sha(encoded({"statement":"b"})))

    def test_interrupted_reservation_never_retries(self):
        with tempfile.TemporaryDirectory() as d:
            runtime = Path(d); out = runtime / "calls/one"; out.mkdir(parents=True)
            forecast.atomic_json(out / "reservation.json", {"id":"one", "kind":"primary"})
            with patch("forecast.urllib.request.urlopen") as transport:
                result = forecast.call_once(runtime, "http://127.0.0.1:1/v1", "one", "x", "primary", time.time()+200)
            transport.assert_not_called()
            self.assertEqual(result["status"], "interrupted_reserved_call")
            self.assertEqual(forecast.call_once(runtime, "ignored", "one", "x", "primary", 0), result)

    def test_no_admission_after_deadline(self):
        with tempfile.TemporaryDirectory() as d, patch("forecast.urllib.request.urlopen") as transport:
            with self.assertRaises(RuntimeError):
                forecast.call_once(Path(d), "http://127.0.0.1:1/v1", "one", "x", "primary", time.time()+1)
            transport.assert_not_called()
            self.assertFalse((Path(d)/"calls/one/reservation.json").exists())


if __name__ == "__main__":
    unittest.main()
