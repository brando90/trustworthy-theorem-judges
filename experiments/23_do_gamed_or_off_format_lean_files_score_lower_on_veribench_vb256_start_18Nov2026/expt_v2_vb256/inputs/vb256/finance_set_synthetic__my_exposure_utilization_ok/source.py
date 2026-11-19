# Synthetic VeriBench task - Inspired by: financial exchange and clearing-house invariants
# Original language: Python
# Category: finance
# Lines: 44
"""Return whether exposure fits the given percentage of the position limit."""

from typing import Callable


def pre_condition(exposure: int, limit: int, threshold: int) -> bool:
    """Return whether exposure and limit are nonnegative and 0 ≤ threshold ≤ 100."""
    return exposure >= 0 and limit >= 0 and 0 <= threshold <= 100


def my_exposure_utilization_ok(exposure: int, limit: int, threshold: int) -> bool:
    """Return whether exposure fits the given percentage of the position limit. Raise
    AssertionError if the input predicate rejects the arguments.
    """
    assert pre_condition(exposure, limit, threshold), "pre violated"
    return exposure * 100 <= limit * threshold


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(70, 100, 80) is True
    assert candidate(85, 100, 80) is False
    assert candidate(80, 100, 80) is True
    assert candidate(0, 100, 0) is True
    assert candidate(1, 0, 100) is False
    return True


if __name__ == "__main__":
    assert check(my_exposure_utilization_ok)
    print(f"All tests passed: {__file__}!")
