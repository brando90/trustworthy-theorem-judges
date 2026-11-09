"""TLDR: Reconstruct three saved bootstrap refits and recorded failures without replacing measured draws."""

import argparse
import json
from pathlib import Path

import numpy as np

from mixture_models import fit_mixture
from verify_training import (METRICS, close, histogram, load, metrics,
                             mixture_certificate, original_partitions, sha256,
                             smoothing)


ROOT = Path(__file__).resolve().parents[1]
DRAW_INDICES = (0, 499, 999)


def verify(data_path, out, private_out, protocol_path):
    """Check recorded resampling wiring; never replace or retry the measured run."""
    cfg, data = load(protocol_path), load(data_path)
    result = load(out / "results.json")
    bootstrap_path = private_out / "bootstrap.json"
    bootstrap = load(bootstrap_path)
    assert result["dataset_sha256"] == cfg["dataset_sha256"] == sha256(data_path)
    assert result["protocol_sha256"] == sha256(protocol_path)
    assert cfg["bootstrap_draws"] == cfg["mixture_refit_bootstrap_draws"] == 1000
    assert cfg["mixture_objectives"] == ["weighted_pmf", "pearson"]
    assert len(bootstrap["ledger"]) == 1000
    assert set(bootstrap["refit_differences"]) == set(METRICS)

    rows = data["rows"]
    target = np.asarray([histogram(row["ratings"]) for row in rows])
    candidates = np.stack([
        smoothing(np.asarray([histogram(values) for values in data["outputs"][name]]),
                  cfg["epsilon"])
        for name in cfg["candidate_order"]
    ], axis=1)
    partitions = original_partitions(rows, cfg["seeds"])
    families = sorted({row["family"] for row in rows})
    family_rows = {family: np.asarray([i for i, row in enumerate(rows) if row["family"] == family])
                   for family in families}
    rng = np.random.default_rng(cfg["bootstrap_seed"])
    failure_indices = tuple(entry["draw"] for entry in bootstrap["ledger"] if not entry["valid"])
    checked_indices = tuple(sorted(set(DRAW_INDICES) | set(failure_indices)))
    selected_draws = {}
    for index in range(cfg["bootstrap_draws"]):
        draw = rng.choice(families, size=len(families), replace=True)
        if index in checked_indices:
            selected_draws[index] = draw

    reports = []
    max_metric_error = 0.0
    total_fits = 0
    total_independent_certificates = 0
    failure_receipts = []
    for draw_index in checked_indices:
        draw = selected_draws[draw_index]
        indices = np.concatenate([family_rows[family] for family in draw])
        values = {objective: [] for objective in cfg["mixture_objectives"]}
        valid = True
        reason = None
        fit_count = 0
        failed_certificates = 0
        independently_verified = 0
        undefined_training_correlations = 0
        certificate_maxima = {}
        for seed_index, (outer, _) in enumerate(partitions):
            forecasts = {objective: np.full((len(indices), 6), np.nan)
                         for objective in cfg["mixture_objectives"]}
            for fold in range(cfg["outer_folds"]):
                train = indices[outer[indices] != fold]
                test_local = np.flatnonzero(outer[indices] == fold)
                test = indices[test_local]
                if not len(test):
                    continue
                if len(train) < 2:
                    valid = False
                    reason = "empty_or_single_row_training"
                    break
                assert not ({rows[i]["family"] for i in train} & {rows[i]["family"] for i in test})
                for objective in cfg["mixture_objectives"]:
                    weights, receipt = fit_mixture(candidates[train], target[train], objective)
                    fit_count += 1
                    undefined_training_correlations += int(receipt["undefined_correlation"])
                    independent_valid, certificate = mixture_certificate(
                        candidates[train], target[train], np.asarray(weights), objective
                    )
                    assert independent_valid == bool(receipt["success"]), (
                        draw_index, fold, objective, receipt, certificate
                    )
                    independently_verified += int(independent_valid)
                    for name, value in certificate.items():
                        if not isinstance(value, bool):
                            certificate_maxima[name] = max(certificate_maxima.get(name, 0.0), abs(float(value)))
                    if not receipt["success"]:
                        # Preserve only aggregate numerical diagnostics, never fitted
                        # weights, individual ratings or item-level predictions.
                        diagnostic_fields = ("objective", "status", "success", "certificate_residual",
                                             "cone_dual_violation", "cone_complementarity", "cone_orthogonality",
                                             "correlation_identity_error", "simplex_frank_wolfe_gap", "tolerances")
                        failure_receipts.append({
                            "draw": draw_index, "method": "mixture_" + objective,
                            "seed_index": seed_index, "seed": cfg["seeds"][seed_index], "fold": fold,
                            "independent_certificate_passed": independent_valid,
                            "independent_certificate": certificate,
                            **{key: receipt[key] for key in diagnostic_fields if key in receipt},
                        })
                        failed_certificates += 1
                        valid = False
                        reason = "optimality_certificate_failed"
                        break
                    assert np.min(weights) >= -1e-10
                    close(weights.sum(), 1.0, "resampled simplex weights", atol=1e-10, rtol=0)
                    # Independent prediction expression rather than production predict_mixture.
                    forecasts[objective][test_local] = np.sum(candidates[test] * weights[None, :, None], axis=1)
                if not valid:
                    break
            if not valid:
                break
            for objective in cfg["mixture_objectives"]:
                assert np.isfinite(forecasts[objective]).all()
                values[objective].append(metrics(target[indices], forecasts[objective]))

        expected_ledger = bootstrap["ledger"][draw_index]
        reconstructed_ledger = {
            "draw": draw_index, "unique_families": len(set(draw)), "valid": valid,
            "reason": reason, "fits": fit_count, "certificate_failures": failed_certificates,
            "undefined_training_correlations": undefined_training_correlations,
        }
        assert expected_ledger == reconstructed_ledger, (expected_ledger, reconstructed_ledger)
        errors = {}
        undefined_metrics = []
        for metric in METRICS:
            difference = (float(np.mean([value[metric] for value in values["weighted_pmf"]])
                                - np.mean([value[metric] for value in values["pearson"]]))
                          if valid else None)
            expected = bootstrap["refit_differences"][metric][draw_index]
            close(difference, expected, f"bootstrap refit {draw_index}: {metric}")
            if difference is not None and expected is not None and np.isfinite(difference):
                error = abs(difference - expected)
                errors[metric] = error
                max_metric_error = max(max_metric_error, error)
            else:
                errors[metric] = None
                undefined_metrics.append(metric)
        total_fits += fit_count
        total_independent_certificates += independently_verified
        reports.append({**reconstructed_ledger, "independently_verified_certificates": independently_verified,
                        "certificate_maximum_residuals": certificate_maxima,
                        "metric_absolute_errors": errors, "undefined_metrics": undefined_metrics})

    return {
        "status": "PASS", "kind": "deterministic_reconstruction_of_existing_resamples",
        "draw_indices": list(checked_indices), "draws_verified": len(reports),
        "prespecified_sample_indices": list(DRAW_INDICES),
        "recorded_failure_draw_indices": list(failure_indices),
        "replayed_failure_receipts": failure_receipts,
        "mixture_fits_reconstructed": total_fits,
        "independent_certificates_passed": total_independent_certificates,
        "metrics_checked_per_draw": list(METRICS), "maximum_metric_absolute_error": max_metric_error,
        "reports": reports, "dataset_sha256": sha256(data_path),
        "protocol_sha256": sha256(protocol_path), "results_sha256": sha256(out / "results.json"),
        "bootstrap_sha256": sha256(bootstrap_path), "verifier_sha256": sha256(__file__),
        "production_mixture_script_sha256": sha256(Path(__file__).parent / "mixture_models.py"),
        "independent_verifier_script_sha256": sha256(Path(__file__).parent / "verify_training.py"),
        "new_resampling_draws": 0, "replaced_resampling_draws": 0, "new_model_calls": 0,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--private-out", type=Path, required=True)
    parser.add_argument("--protocol", type=Path, default=ROOT / "protocol.json")
    args = parser.parse_args()
    report = verify(args.data, args.out, args.private_out, args.protocol)
    (args.out / "verification_refit_samples.json").write_text(json.dumps(report, indent=2, allow_nan=False) + "\n")
    print(json.dumps(report, indent=2, allow_nan=False))


if __name__ == "__main__":
    main()
