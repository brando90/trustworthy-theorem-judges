# Synthetic VeriBench task -- Inspired by: Minimum Drug Dose Interval Gate (FDA 21 CFR 820)
# Original language: Python
# Category: 05_regulated
"""Synthetic dose-interval predicate comparing supplied minute values. Return whether last_min plus
min_interval is at most now_min. Negative inputs raise AssertionError.
"""

from typing import Callable


def pre_condition(now_min: int, last_min: int, min_interval: int) -> bool:
    """Return whether now_min, last_min and min_interval are nonnegative."""
    return now_min >= 0 and last_min >= 0 and min_interval >= 0


def my_dose_interval_ok(now_min: int, last_min: int, min_interval: int) -> bool:
    """Return whether at least the required interval in minutes has elapsed since the last dose.
    Raise AssertionError if the input predicate rejects the arguments.

    The input check requires that now_min, last_min and min_interval are nonnegative. A failed
    check raises AssertionError.
    """
    assert pre_condition(now_min, last_min, min_interval), "pre violated"
    return bool(last_min + min_interval <= now_min)


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(160, 100, 60) is True
    assert candidate(100, 100, 0) is True
    assert candidate(130, 100, 60) is False
    assert candidate(0, 0, 1) is False
    try:
        candidate(-1, 0, 0)
    except AssertionError:
        pass
    else:
        raise AssertionError('expected AssertionError')
    return True


if __name__ == "__main__":
    assert check(my_dose_interval_ok)
    print(f"All tests passed: {__file__}!")
