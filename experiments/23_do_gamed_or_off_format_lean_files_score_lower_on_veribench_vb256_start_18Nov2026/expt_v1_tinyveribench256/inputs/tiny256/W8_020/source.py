# File: humaneval_32_poly.py
# HumanEval problem HumanEval/32

"""Polynomial evaluation and bisection root finding from a coefficient list, with unit tests."""

import math


def poly(xs: list, x: float):
    """Evaluate coefficients xs in increasing degree order by summing coeff * math.pow(x, i) for
    each index i. An empty list returns integer zero. Computation uses floating-point powers and
    may raise their domain or overflow errors.
    """
    return sum([coeff * math.pow(x, i) for i, coeff in enumerate(xs)])


def find_zero(xs: list):
    """Expand the initial interval [-1, 1] by doubling its endpoints while computed endpoint values
    have positive product, then bisect until interval width is at most 1e-10 and return the left
    endpoint. Coefficient count is unrestricted. Empty or all-zero coefficients return -1.0.
    Termination and root accuracy are not guaranteed. Arithmetic errors may propagate.
    """
    begin, end = -1., 1.
    while poly(xs, begin) * poly(xs, end) > 0:
        begin *= 2.0
        end *= 2.0
    while end - begin > 1e-10:
        center = (begin + end) / 2.0
        if poly(xs, center) * poly(xs, begin) > 0:
            begin = center
        else:
            end = center
    return begin

# Test function


METADATA = {}


def check(candidate):
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    from math import isclose

    assert isclose(candidate([-2.0, 1.0]), 2.0, rel_tol=0.0, abs_tol=0.0001)
    assert isclose(candidate([0.0, 1.0]), 0.0, rel_tol=0.0, abs_tol=0.0001)
    assert isclose(candidate([3.0, 1.0]), -(3.0), rel_tol=0.0, abs_tol=0.0001)
    assert candidate([]) == -1.0
    assert candidate([0.0]) == -1.0



# Run tests
if __name__ == "__main__":
    check(find_zero)
    print("All tests passed!")
