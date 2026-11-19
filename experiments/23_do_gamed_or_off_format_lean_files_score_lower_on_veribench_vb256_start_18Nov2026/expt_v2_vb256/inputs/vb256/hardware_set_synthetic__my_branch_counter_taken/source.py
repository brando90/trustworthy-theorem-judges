# Synthetic VeriBench task — Inspired by: two-bit branch counter predict-taken
# Original language: Python
# Category: 09_hardware
"""Two-bit saturating branch predictor readout: counters 2 and 3 predict taken."""

from typing import Callable


def pre_condition(counter: int) -> bool:
    """Return whether 0 ≤ counter ≤ 3."""
    return 0 <= counter <= 3


def my_branch_counter_taken(counter: int):
    """Return whether counter is at least 2, representing a taken prediction. Require 0 ≤ counter ≤
    3. Otherwise raise AssertionError. No integer type check is performed, so fractional values
    and booleans satisfying the bounds are also accepted.
    """
    assert pre_condition(counter), "pre violated"
    return counter >= 2


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(0) is False
    assert candidate(1) is False
    assert candidate(2) is True
    assert candidate(3) is True
    try:
        candidate(-1)
    except AssertionError:
        pass
    else:
        raise AssertionError("expected AssertionError")
    return True


if __name__ == "__main__":
    assert check(my_branch_counter_taken)
    print(f"All tests passed: {__file__}!")
