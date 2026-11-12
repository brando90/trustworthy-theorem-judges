"""TLDR: Synthetic known-answer and integrity controls for the offline six-probability scaffold."""
import copy
import hashlib
import json
import math
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scaffold import (MAX_RESPONSE_BYTES, VISIBILITY, artifact_metrics, evaluate,
                      correlations, freeze_manifest, parse_prediction, verify_manifest)


class ScaffoldTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def fixture(self, count=2, method="method_2_correlation"):
        artifacts = []
        for i in range(count):
            files = {}
            for role, text in {"python_source": "def f(x): return x\n", "candidate_lean": "theorem t : True := by trivial\n",
                               "gold_reference_lean": "theorem t : True := by trivial\n", "rubric": "Synthetic parser control, not a semantic benchmark.\n"}.items():
                name = f"{i}_{role}.txt"
                (self.root / name).write_text(text + f"-- synthetic item {i}\n")
                files[role] = name
            artifacts.append({"artifact_id": f"a{i}", "task_family_id": f"f{i}", "agent_id": "synthetic_agent", "files": files})
        spec = {"condition_id": "synthetic_control", "split": "train", "proof_visibility": VISIBILITY,
                "judge_configuration": {"judge_id": "synthetic_judge", "model_id": "none_synthetic",
                                        "harness": "offline_control", "effort": "not_applicable",
                                        "training_method": method, "prompt_sha256": hashlib.sha256(b"synthetic prompt").hexdigest()},
                "artifacts": artifacts}
        return spec, freeze_manifest(spec, self.root)

    def responses(self, manifest, forecasts):
        return [{"artifact_id": item["artifact_id"], "input_sha256": item["input_sha256"],
                 "manifest_sha256": manifest["manifest_sha256"],
                 "response": json.dumps({"probabilities": q, "rationale": "Synthetic."})}
                for item, q in zip(manifest["artifacts"], forecasts)]

    def ratings(self, manifest, values):
        return [{"artifact_id": item["artifact_id"], "input_sha256": item["input_sha256"],
                 "rater_id": f"synthetic_rater_{j}", "rating": value}
                for item, group in zip(manifest["artifacts"], values) for j, value in enumerate(group)]

    def test_oracle_and_opposite_endpoint(self):
        q = [1, 0, 0, 0, 0, 0]
        perfect = artifact_metrics(q, [0])
        wrong = artifact_metrics(q, [5])
        for key in ("rps", "brier", "ce", "tvd", "kl_human_to_judge", "empirical_cdf_squared_distance", "squared_mean_error", "mae", "bias"):
            self.assertEqual(perfect[key], 0)
        self.assertEqual(wrong["rps"], 1)
        self.assertEqual(wrong["brier"], 2)
        self.assertEqual(wrong["tvd"], 1)
        self.assertTrue(math.isinf(wrong["ce"]))
        self.assertEqual(wrong["bias"], -1)

    def test_individual_rating_rps_identity(self):
        for q, ratings in [([0.5, 0, 0, 0, 0, 0.5], [0, 5]),
                           ([0.1, 0.2, 0.1, 0.3, 0.2, 0.1], [1, 1, 4]),
                           ([0, 0, 1, 0, 0, 0], [0, 2, 5])]:
            m = artifact_metrics(q, ratings)
            self.assertAlmostEqual(m["rps"], m["empirical_cdf_squared_distance"] + m["empirical_disagreement"])
        m = artifact_metrics([0.5, 0, 0, 0, 0, 0.5], [0, 5])
        self.assertEqual(m["empirical_cdf_squared_distance"], 0)
        self.assertEqual(m["rps"], 0.25)
        self.assertAlmostEqual(m["ce"], math.log(2))
        self.assertAlmostEqual(m["kl_human_to_judge"], 0)
        self.assertEqual(m["brier"], 0.5)

    def test_tvd_uses_empirical_histogram_not_individual_point_masses(self):
        q = [0.5, 0, 0, 0, 0, 0.5]
        self.assertEqual(artifact_metrics(q, [0, 5])["tvd"], 0)
        self.assertEqual(artifact_metrics(q, [0, 0, 0, 5])["tvd"], 0.25)
        # Averaging distances to individual point masses would incorrectly give 0.5.
        self.assertEqual(artifact_metrics([0, 0.5, 0, 0, 0.5, 0], [0, 5])["tvd"], 1)

    def test_artifact_weighting_and_root_metric_crosswalk(self):
        _, manifest = self.fixture()
        responses = self.responses(manifest, [[1, 0, 0, 0, 0, 0]] * 2)
        report = evaluate(manifest, responses, self.ratings(manifest, [[0], [5, 5, 5]]), self.root)
        m = report["scored_artifacts_only"]
        self.assertEqual(m["rps"], 0.5)  # Not the rating-weighted 0.75.
        self.assertEqual(m["tvd"], 0.5)
        self.assertEqual(report["full_denominator_bounds"]["tvd"], {"lower": 0.5, "upper": 0.5})
        self.assertEqual(m["brier"], 1)
        self.assertEqual(m["ce"], "Infinity")
        self.assertAlmostEqual(m["nrmse"], math.sqrt(0.5))
        self.assertAlmostEqual(m["root_mean_cdf_distance"], math.sqrt(0.5))
        self.assertIsNone(m["pearson"])
        self.assertTrue(report["point_estimates_cover_full_manifest"])
        self.assertEqual(report["counts"]["zero_probability_ratings_scored"], 3)

    def test_matched_artifacts_give_same_rps_and_distance_difference(self):
        ratings = [0, 0, 3, 5]
        a = artifact_metrics([0.2, 0.2, 0.1, 0.2, 0.1, 0.2], ratings)
        b = artifact_metrics([0.1, 0.1, 0.2, 0.2, 0.3, 0.1], ratings)
        self.assertAlmostEqual(a["rps"] - b["rps"], a["empirical_cdf_squared_distance"] - b["empirical_cdf_squared_distance"])

    def test_strict_parser_rejects_malformed_forecasts(self):
        bad = ["", " ", "```json\n{}\n```", '{"probabilities":[1,0,0,0,0,0],"rationale":"a","rationale":"b"}',
               '{"probabilities":[NaN,0,0,0,0,0],"rationale":"x"}',
               '{"probabilities":[Infinity,0,0,0,0,0],"rationale":"x"}',
               '{"probabilities":[true,0,0,0,0,0],"rationale":"x"}',
               '{"probabilities":[1.1,-0.1,0,0,0,0],"rationale":"x"}',
               '{"probabilities":[0.2,0.2,0.2,0.2,0.2,0.00000000001],"rationale":"x"}',
               '{"probabilities":[0.2,0.2,0.2,0.2,0.2],"rationale":"x"}',
               '{"probabilities":[1,0,0,0,0,0],"rationale":false}',
               '{"probabilities":[1,0,0,0,0,0],"rationale":"x","extra":1}',
               "x" * (MAX_RESPONSE_BYTES + 1)]
        for raw in bad:
            with self.subTest(raw=raw[:60]), self.assertRaises((ValueError, TypeError)):
                parse_prediction(raw)
        raw = '{"probabilities":[0.1,0.2,0.3,0.1,0.2,0.1],"rationale":"x"}'
        self.assertEqual(parse_prediction(raw), [0.1, 0.2, 0.3, 0.1, 0.2, 0.1])

    def test_tiny_probability_is_not_floored(self):
        tiny = "0." + "0" * 49 + "1"
        remainder = "0." + "9" * 50
        q = parse_prediction('{"probabilities":[' + tiny + ',' + remainder + ',0,0,0,0],"rationale":"x"}')
        self.assertAlmostEqual(artifact_metrics(q, [0])["ce"], 50 * math.log(10))

    def test_failed_missing_and_unrated_keep_full_denominator(self):
        _, manifest = self.fixture(4)
        responses = self.responses(manifest, [[1, 0, 0, 0, 0, 0]] * 3)
        responses[1]["response"] = ""
        responses[2].pop("response")
        responses[2]["error"] = "transport_timeout"
        report = evaluate(manifest, responses, self.ratings(manifest, [[0], [0], [0], [0]]), self.root)
        self.assertEqual(report["counts"]["response_statuses"], {"ok": 1, "invalid": 1, "error": 1, "missing": 1})
        self.assertEqual(report["counts"]["scheduled_artifacts"], 4)
        self.assertEqual(report["counts"]["scored_artifacts"], 1)
        self.assertEqual(report["full_denominator_bounds"]["rps"], {"lower": 0, "upper": 0.75})
        self.assertEqual(report["full_denominator_bounds"]["tvd"], {"lower": 0, "upper": 0.75})
        self.assertEqual(report["full_denominator_bounds"]["brier"]["upper"], 1.5)
        self.assertEqual(report["full_denominator_bounds"]["ce"]["upper"], "Infinity")
        self.assertFalse(report["point_estimates_cover_full_manifest"])
        report = evaluate(manifest, self.responses(manifest, [[1, 0, 0, 0, 0, 0]] * 4), [], self.root)
        self.assertIsNone(report["scored_artifacts_only"])
        self.assertEqual(report["full_denominator_bounds"]["rps"], {"lower": 0, "upper": 1})
        self.assertEqual(report["full_denominator_bounds"]["tvd"], {"lower": 0, "upper": 1})

    def test_zero_probability_and_missing_do_not_make_nan(self):
        _, manifest = self.fixture(2)
        report = evaluate(manifest, self.responses(manifest, [[1, 0, 0, 0, 0, 0]]), self.ratings(manifest, [[5], [0]]), self.root)
        self.assertEqual(report["full_denominator_bounds"]["ce"], {"lower": "Infinity", "upper": "Infinity"})
        self.assertEqual(report["full_denominator_bounds"]["tvd"], {"lower": 0.5, "upper": 1})
        json.dumps(report, allow_nan=False)

    def test_duplicate_unknown_and_misbound_responses_fail(self):
        _, manifest = self.fixture(3)
        responses = self.responses(manifest, [[1, 0, 0, 0, 0, 0]])
        for changed in [responses * 2, [{**responses[0], "artifact_id": "unknown"}],
                        [{**responses[0], "manifest_sha256": "0" * 64}],
                        [{**responses[0], "input_sha256": "0" * 64}]]:
            with self.assertRaises(ValueError):
                evaluate(manifest, changed, [], self.root)

    def test_rating_integrity(self):
        _, manifest = self.fixture()
        ratings = self.ratings(manifest, [[0]])
        changes = [ratings * 2, [{**ratings[0], "rating": True}], [{**ratings[0], "rating": 6}],
                   [{**ratings[0], "rating": 2.0}], [{**ratings[0], "input_sha256": "0" * 64}],
                   [{**ratings[0], "artifact_id": "unknown"}]]
        for changed in changes:
            with self.assertRaises(ValueError):
                evaluate(manifest, [], changed, self.root)

    def test_manifest_detects_input_and_metadata_mutation(self):
        spec, manifest = self.fixture()
        verify_manifest(manifest, self.root)
        bad = copy.deepcopy(manifest)
        bad["split"] = "test"
        with self.assertRaises(ValueError):
            verify_manifest(bad, self.root)
        (self.root / spec["artifacts"][0]["files"]["candidate_lean"]).write_text("changed")
        with self.assertRaises(ValueError):
            verify_manifest(manifest, self.root)

    def test_manifest_rejects_duplicate_and_escaping_paths(self):
        spec, _ = self.fixture()
        bad = copy.deepcopy(spec)
        bad["artifacts"].append(bad["artifacts"][0])
        with self.assertRaises(ValueError):
            freeze_manifest(bad, self.root)
        spec["artifacts"][0]["files"]["python_source"] = "../outside"
        with self.assertRaises(ValueError):
            freeze_manifest(spec, self.root)

    def test_both_training_methods_use_same_evaluation(self):
        spec, manifest2 = self.fixture(method="method_2_correlation")
        spec["judge_configuration"]["training_method"] = "method_4_proper_loss"
        manifest4 = freeze_manifest(spec, self.root)
        q = [[0.1, 0.2, 0.3, 0.1, 0.2, 0.1]] * 2
        reports = [evaluate(m, self.responses(m, q), self.ratings(m, [[1, 2], [3, 5]]), self.root) for m in (manifest2, manifest4)]
        self.assertEqual(reports[0]["scored_artifacts_only"], reports[1]["scored_artifacts_only"])
        self.assertIn("tvd", reports[0]["scored_artifacts_only"])
        self.assertNotEqual(reports[0]["manifest_sha256"], reports[1]["manifest_sha256"])

    def test_all_correlations_preserve_ties(self):
        result, status = correlations([0, 0, 1], [0, 1, 1])
        self.assertAlmostEqual(result["pearson"], 0.5)
        if status["status"].startswith("unavailable"):
            self.skipTest("SciPy unavailable; explicit missing status verified")
        self.assertAlmostEqual(result["spearman"], 0.5)
        self.assertAlmostEqual(result["kendall_tau_b"], 0.5)
        self.assertIsNotNone(status["scipy_version"])

    def test_optional_scipy_absence_is_explicit(self):
        from unittest.mock import patch
        with patch.dict(sys.modules, {"scipy": None}):
            result, status = correlations([0, 1], [0, 1])
        self.assertEqual(result["pearson"], 1)
        self.assertIsNone(result["spearman"])
        self.assertIsNone(result["kendall_tau_b"])
        self.assertTrue(status["status"].startswith("unavailable"))

    def test_cli_writes_standard_json_and_refuses_overwrite(self):
        spec, manifest = self.fixture(1)
        for name, value in {"spec": spec, "manifest": manifest,
                            "responses": self.responses(manifest, [[1, 0, 0, 0, 0, 0]]),
                            "ratings": self.ratings(manifest, [[5]])}.items():
            (self.root / (name + ".json")).write_text(json.dumps(value))
        script = Path(__file__).with_name("scaffold.py")
        out = self.root / "report.json"
        command = [sys.executable, str(script), "evaluate", "--input-root", str(self.root), "--out", str(out)]
        for name in ("manifest", "responses", "ratings"):
            command += ["--" + name, str(self.root / (name + ".json"))]
        subprocess.run(command, check=True, capture_output=True)
        report = json.loads(out.read_text())
        self.assertEqual(report["scored_artifacts_only"]["ce"], "Infinity")
        self.assertEqual(report["scored_artifacts_only"]["tvd"], 1)
        self.assertEqual(report["metrics_version"], "native_probability_metrics_v2")
        self.assertNotEqual(subprocess.run(command, capture_output=True).returncode, 0)


if __name__ == "__main__":
    unittest.main()
