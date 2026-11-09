"""TLDR: Fit centered six-category probability heads with weighted PMF and proper losses."""

import argparse
import json

import numpy as np
from scipy.optimize import minimize
from scipy.special import log_softmax, softmax


LOSSES = ("weighted_pmf", "ce", "brier", "rps")
N_CATEGORIES = 6
GRID = np.arange(N_CATEGORIES, dtype=float) / (N_CATEGORIES - 1)


def zero_sum_basis():
    """Return a fixed orthonormal basis for centered six-class coefficient rows."""
    basis = np.zeros((N_CATEGORIES, N_CATEGORIES - 1))
    for k in range(1, N_CATEGORIES):
        denominator = np.sqrt(k * (k + 1))
        basis[:k, k - 1] = 1.0 / denominator
        basis[k, k - 1] = -k / denominator
    return basis


BASIS = zero_sum_basis()


def _validate_inputs(x, p):
    x, p = np.asarray(x, dtype=float), np.asarray(p, dtype=float)
    if x.ndim != 2 or p.shape != (len(x), N_CATEGORIES) or not len(x):
        raise ValueError("Expected nonempty feature rows and matching six-category targets")
    if not np.isfinite(x).all() or not np.isfinite(p).all():
        raise ValueError("Inputs and targets must be finite")
    if np.any(p < 0) or not np.allclose(p.sum(axis=1), 1.0, atol=1e-12, rtol=0):
        raise ValueError("Each target must be a probability vector")
    return x, p


def probability_loss(p, q, loss):
    """Return equal-row mean loss; Brier/RPS average over individual human ratings."""
    p, q = np.asarray(p, dtype=float), np.asarray(q, dtype=float)
    if loss == "weighted_pmf":
        return float(np.mean(np.sum(p * (p - q) ** 2, axis=1)))
    if loss == "ce":
        # Fit uses stable log-softmax instead; this helper is for valid positive q.
        if np.any(q <= 0):
            raise ValueError("Cross-entropy requires positive predicted probabilities")
        return float(-np.mean(np.sum(p * np.log(q), axis=1)))
    if loss == "brier":
        return float(np.mean(1 + np.sum(q * q - 2 * p * q, axis=1)))
    if loss == "rps":
        fp, fq = np.cumsum(p, axis=1)[:, :-1], np.cumsum(q, axis=1)[:, :-1]
        return float(np.mean(fq * fq - 2 * fq * fp + fp))
    raise ValueError(f"Unknown fitting loss: {loss}")


def objective(theta, x, p, loss, strength):
    """Return loss and analytic gradient for a supplied design including any intercept.

    theta contains design_columns * 5 orthonormal coordinates. Expanding through
    BASIS produces design_columns * 6 coefficients whose class-wise rows sum to
    zero, so there are no optimizer directions that add an irrelevant logit offset.
    The L2 penalty is the full centered coefficient squared norm / 2; orthonormal
    coordinates make that exactly the reduced-coordinate squared norm / 2.
    """
    if loss not in LOSSES:
        raise ValueError(f"Unknown fitting loss: {loss}")
    if not np.isfinite(strength) or strength < 0:
        raise ValueError("Penalty strength must be finite and nonnegative")
    coordinates = np.asarray(theta).reshape(x.shape[1], N_CATEGORIES - 1)
    weights = coordinates @ BASIS.T
    logits = x @ weights
    q = softmax(logits, axis=1)
    n = len(x)
    if loss == "ce":
        value = -np.sum(p * log_softmax(logits, axis=1)) / n
        gz = (q - p) / n
    else:
        value = probability_loss(p, q, loss)
        if loss == "weighted_pmf":
            gq = 2 * p * (q - p) / n
        elif loss == "brier":
            gq = 2 * (q - p) / n
        else:
            fp = np.cumsum(p, axis=1)[:, :-1]
            fq = np.cumsum(q, axis=1)[:, :-1]
            gq = np.zeros_like(q)
            threshold_gradient = 2 * (fq - fp) / ((N_CATEGORIES - 1) * n)
            gq[:, :-1] = np.cumsum(threshold_gradient[:, ::-1], axis=1)[:, ::-1]
        gz = q * (gq - np.sum(q * gq, axis=1, keepdims=True))
    penalty = strength * np.sum(coordinates * coordinates) / 2
    gradient = (x.T @ gz) @ BASIS + strength * coordinates
    return float(value + penalty), gradient.ravel()


def fit(x, p, loss, strength, seed, config):
    """Fit only the supplied training rows; return a serializable model and receipt.

    Required config keys: maxiter, maxfun, ftol, gtol. Optional keys: maxls (20)
    and init_std (0.02). A failed but finite fit is returned with success=False;
    callers must retain that status rather than silently retrying or dropping it.
    """
    x, p = _validate_inputs(x, p)
    if loss not in LOSSES:
        raise ValueError(f"Unknown fitting loss: {loss}")
    options = {key: config[key] for key in ("maxiter", "maxfun", "ftol", "gtol")}
    options["maxls"] = config.get("maxls", 20)
    for key in ("maxiter", "maxfun", "maxls"):
        if not isinstance(options[key], int) or isinstance(options[key], bool) or options[key] < 1:
            raise ValueError(f"{key} must be a positive integer")
    for key in ("ftol", "gtol"):
        if not np.isfinite(options[key]) or options[key] <= 0:
            raise ValueError(f"{key} must be finite and positive")
    init_std = float(config.get("init_std", 0.02))
    if not np.isfinite(init_std) or init_std < 0:
        raise ValueError("init_std must be finite and nonnegative")

    mean = x.mean(axis=0)
    sd = np.maximum(x.std(axis=0), 1e-8)
    design = np.column_stack([np.ones(len(x)), (x - mean) / sd])
    raw_initial = np.random.default_rng(seed).normal(
        0, init_std, size=(design.shape[1], N_CATEGORIES)
    )
    # Project the same isotropic six-class initialization onto the centered gauge.
    initial = (raw_initial @ BASIS).ravel()
    optimum = minimize(
        objective, initial, args=(design, p, loss, strength), method="L-BFGS-B",
        jac=True, options=options,
    )
    coordinates = optimum.x.reshape(design.shape[1], N_CATEGORIES - 1)
    weights = coordinates @ BASIS.T
    q = softmax(design @ weights, axis=1)
    value, gradient = objective(optimum.x, design, p, loss, strength)
    finite = bool(np.isfinite(optimum.x).all() and np.isfinite(q).all()
                  and np.isfinite(value) and np.isfinite(gradient).all())
    data_value = (float(-np.mean(np.sum(p * log_softmax(design @ weights, axis=1), axis=1)))
                  if loss == "ce" else probability_loss(p, q, loss))
    model = {"mean": mean.tolist(), "sd": sd.tolist(), "weights": weights.tolist(),
             "coordinates": coordinates.tolist(), "basis": "helmert_zero_sum_v1",
             "loss": loss, "strength": float(strength)}
    receipt = {
        "optimizer": "L-BFGS-B", "loss": loss, "strength": float(strength),
        "seed": int(seed), "success": bool(optimum.success), "status": int(optimum.status),
        "message": str(optimum.message), "iterations": int(optimum.nit),
        "function_calls": int(optimum.nfev), "gradient_calls": int(optimum.njev),
        "finite": finite, "objective": float(value), "data_loss": data_value,
        "penalty": float(strength * np.sum(coordinates * coordinates) / 2),
        "gradient_norm_l2": float(np.linalg.norm(gradient)),
        "gradient_norm_inf": float(np.max(np.abs(gradient))),
        "train_expected_rating_sd": float(np.std(q @ GRID)),
        "max_probability_sum_error": float(np.max(np.abs(q.sum(axis=1) - 1))),
        "max_coefficient_row_sum_abs": float(np.max(np.abs(weights.sum(axis=1)))),
        "training_rows": len(x), "input_features": x.shape[1],
        "optimized_parameters": int(coordinates.size), "stored_coefficients": int(weights.size),
        "optimizer_options": options, "init_std": init_std,
    }
    return model, receipt


def predict(model, x):
    """Predict six probabilities using the stored training-only transformation."""
    x = np.asarray(x, dtype=float)
    mean, sd, weights = (np.asarray(model[key], dtype=float) for key in ("mean", "sd", "weights"))
    if x.ndim != 2 or x.shape[1] != len(mean) or not np.isfinite(x).all():
        raise ValueError("Prediction features must be finite and match fitted feature count")
    design = np.column_stack([np.ones(len(x)), (x - mean) / sd])
    return softmax(design @ weights, axis=1)


def controls():
    """Check synthetic derivatives, gauge, proper-loss values and weighted fitting."""
    assert np.allclose(BASIS.T @ BASIS, np.eye(5), atol=1e-14, rtol=0)
    assert np.allclose(BASIS.sum(axis=0), 0, atol=1e-14, rtol=0)
    rng = np.random.default_rng(13)
    design = np.column_stack([np.ones(8), rng.normal(size=(8, 2))])
    p = rng.dirichlet(np.ones(6), size=8)
    theta = rng.normal(0, 0.2, size=design.shape[1] * 5)
    gradient_errors = {}
    step = 1e-6
    for loss in LOSSES:
        _, analytic = objective(theta, design, p, loss, 0.01)
        numerical = np.empty_like(theta)
        for k in range(len(theta)):
            direction = np.zeros_like(theta)
            direction[k] = step
            plus = objective(theta + direction, design, p, loss, 0.01)[0]
            minus = objective(theta - direction, design, p, loss, 0.01)[0]
            numerical[k] = (plus - minus) / (2 * step)
        error = float(np.max(np.abs(analytic - numerical)))
        assert error < 1e-7, (loss, error)
        gradient_errors[loss] = error

    # With an identity design, centered log probabilities exactly reproduce p.
    exact_p = rng.dirichlet(np.ones(6), size=3)
    logp = np.log(exact_p)
    exact_theta = (logp @ BASIS).ravel()
    oracle_value, oracle_gradient = objective(exact_theta, np.eye(3), exact_p, "weighted_pmf", 0)
    assert oracle_value < 1e-28 and np.linalg.norm(oracle_gradient) < 1e-14
    shifted = logp + np.array([[3.0], [-7.0], [2.0]])
    assert np.allclose(softmax(logp, axis=1), softmax(shifted, axis=1), atol=1e-14, rtol=0)
    assert np.allclose(logp @ BASIS, shifted @ BASIS, atol=1e-14, rtol=0)

    # Independent one-hot expectation calculations verify Brier and ordinal scores.
    q = softmax(design @ (theta.reshape(3, 5) @ BASIS.T), axis=1)
    brier_direct, rps_direct = [], []
    for target, forecast in zip(p, q):
        brier_direct.append(sum(target[r] * np.sum((forecast - np.eye(6)[r]) ** 2) for r in range(6)))
        rps_direct.append(sum(target[r] * np.mean((np.cumsum(forecast)[:-1]
                          - (np.arange(5) >= r)) ** 2) for r in range(6)))
    assert abs(probability_loss(p, q, "brier") - np.mean(brier_direct)) < 1e-14
    assert abs(probability_loss(p, q, "rps") - np.mean(rps_direct)) < 1e-14

    features = np.array([[-1.0], [1.0]])
    targets = np.eye(6)[[0, 5]]
    config = {"maxiter": 300, "maxfun": 600, "ftol": 1e-12, "gtol": 1e-8}
    model, receipt = fit(features, targets, "weighted_pmf", 0, 17, config)
    predictions = predict(model, features)
    fitted_loss = probability_loss(targets, predictions, "weighted_pmf")
    assert receipt["finite"] and receipt["success"] and fitted_loss < 1e-6, receipt
    assert np.allclose(predictions.sum(axis=1), 1.0, atol=1e-14, rtol=0)
    assert receipt["max_coefficient_row_sum_abs"] < 1e-12
    stored_mean, stored_sd = np.asarray(model["mean"]), np.asarray(model["sd"])
    assert np.array_equal(stored_mean, features.mean(axis=0))
    assert np.array_equal(stored_sd, features.std(axis=0))
    # Prediction cannot refit its transformation from the inference batch.
    alone = predict(model, features[:1])
    together = predict(model, np.vstack([features[:1], [[1000.0]]]))[:1]
    assert np.allclose(alone, together, atol=1e-14, rtol=0)

    return {"status": "PASS", "gradient_max_absolute_errors": gradient_errors,
            "weighted_oracle_value": float(oracle_value),
            "weighted_oracle_gradient_norm": float(np.linalg.norm(oracle_gradient)),
            "two_example_weighted_loss": fitted_loss,
            "two_example_fit": receipt, "gauge_rank": int(np.linalg.matrix_rank(BASIS)),
            "one_hot_expectation_checks": "PASS", "train_only_scaling_check": "PASS"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--controls-only", action="store_true", required=True)
    parser.parse_args()
    print(json.dumps(controls(), indent=2, allow_nan=False))


if __name__ == "__main__":
    main()
