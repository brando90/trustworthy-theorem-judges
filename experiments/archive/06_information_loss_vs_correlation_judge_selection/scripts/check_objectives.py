#!/usr/bin/env python3
"""TLDR: Verify objective identities and a counterexample without models or human data."""
import json
import math


def brier_expected(p, q):
    return sum(p[y] * sum((q[r] - int(r == y)) ** 2 for r in range(len(p)))
               for y in range(len(p)))


def main():
    p = [0.6, 0.3, 0.1]
    q = [2 / 3, 1 / 3, 0.0]
    single_term = lambda forecast: sum(p[r] * (1 - forecast[r]) ** 2 for r in range(3))
    weighted_population = lambda forecast: sum(p[r] * (p[r] - forecast[r]) ** 2 for r in range(3))
    rhs = sum((p[r] - q[r]) ** 2 for r in range(3)) + 1 - sum(x*x for x in p)
    assert math.isclose(brier_expected(p, q), rhs)
    assert brier_expected(p, p) < brier_expected(p, q)
    assert single_term(q) < single_term(p)
    assert weighted_population(p) == 0 < weighted_population(q)
    entropy = -sum(x * math.log(x) for x in p)
    candidates = [[0.5, 0.3, 0.2], [0.4, 0.4, 0.2], p]
    ce = [-sum(p[r] * math.log(c[r]) for r in range(3)) for c in candidates]
    kl = [sum(p[r] * math.log(p[r] / c[r]) for r in range(3)) for c in candidates]
    assert all(math.isclose(a, entropy + b) for a, b in zip(ce, kl))
    assert sorted(range(3), key=ce.__getitem__) == sorted(range(3), key=kl.__getitem__)
    print(json.dumps({
        "kind": "deterministic mathematical controls, not empirical study",
        "all_pass": True,
        "expected_brier_at_truth": brier_expected(p, p),
        "expected_brier_at_alternative": brier_expected(p, q),
        "single_term_loss_at_truth": single_term(p),
        "single_term_loss_at_alternative": single_term(q),
        "ce_forward_kl_same_selection": True,
    }, indent=2))


if __name__ == "__main__":
    main()
