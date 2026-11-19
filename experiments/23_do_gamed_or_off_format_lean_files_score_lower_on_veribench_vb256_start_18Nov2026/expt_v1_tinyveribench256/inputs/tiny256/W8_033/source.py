"""Polynomial evaluation with coefficients in increasing degree order, plus a bounded
floating-point bisection routine. Input validation checks types, endpoint ordering, nonnegative
fuel, and a nonpositive computed endpoint product. These checks do not guarantee a mathematical
root or numerical accuracy.
"""

from typing import Callable, List

# -- Implementation --

def pre(xs: List[float], a: float, b: float, fuel: int) -> bool:
    """Check that xs is a nonempty list of int/float coefficients, a and b are int/float with a <
    b, fuel is a nonnegative int, and the computed endpoint-value product is <= 0. Booleans
    satisfy these type checks. Return a boolean unless polynomial evaluation raises. Finiteness
    is not required.
    """
    return (
        isinstance(xs, list)
        and len(xs) > 0
        and all(isinstance(c, (int, float)) for c in xs)
        and isinstance(a, (int, float))
        and isinstance(b, (int, float))
        and isinstance(fuel, int) and fuel >= 0
        and a < b
        and poly(xs, a) * poly(xs, b) <= 0
    )

def poly(xs: List[float], x: float) -> float:
    """Value at x of the polynomial whose coefficients xs are listed from lowest to highest degree."""
    acc = 0.0
    p = 1.0
    for c in xs:
        acc += float(c) * p
        p *= float(x)
    return acc

def find_zero(xs: List[float], a: float, b: float, fuel: int) -> float:
    """Require pre to succeed, otherwise raise ValueError. Evaluation exceptions propagate. Perform
    at most fuel floating-point bisection steps, returning a midpoint early when its computed
    polynomial magnitude is below 1e-10, otherwise the final midpoint. Zero fuel returns the
    initial midpoint. No root accuracy or finiteness guarantee is enforced.
    """
    if not pre(xs, a, b, fuel):
        raise ValueError("Invalid inputs or bracket does not contain a root")

    left, right = float(a), float(b)
    for _ in range(fuel):
        mid = (left + right) / 2.0
        f_mid = poly(xs, mid)
        if abs(f_mid) < 1e-10:
            return mid
        if poly(xs, left) * f_mid <= 0:
            right = mid
        else:
            left = mid
    return (left + right) / 2.0


# -- Tests --

def check(candidate: Callable[[List[float], float, float, int], float]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    from math import isclose

    assert isclose(candidate([1.0, 2.0], -1.0, 0.0, 100), -(0.5), rel_tol=0.0, abs_tol=0.01)
    assert isclose(candidate([-4.0, 0.0, 1.0], 1.0, 3.0, 100), 2.0, rel_tol=0.0, abs_tol=0.01)
    assert isclose(candidate([0.0, 1.0], -1.0, 1.0, 100), 0.0, rel_tol=0.0, abs_tol=0.01)
    assert candidate([0.0, 1.0], -1.0, 1.0, 0) == 0.0
    assert candidate([1.0, 2.0], -1.0, 3.0, 100) == -0.5
    return True

if __name__ == "__main__":
    assert check(find_zero), f"Failed: {__file__}"
    print("All tests passed.")

