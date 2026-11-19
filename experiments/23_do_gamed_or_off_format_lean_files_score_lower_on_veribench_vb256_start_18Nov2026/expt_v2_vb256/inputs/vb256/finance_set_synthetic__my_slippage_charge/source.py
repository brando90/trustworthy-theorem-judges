# Synthetic VeriBench task - Inspired by: financial exchange and clearing-house invariants
# Original language: Python
# Category: finance
# Lines: 36
"""Return the base charge plus quantity times the per-unit tier charge, in basis points."""

from typing import Callable


def pre_condition(base_bps: int, qty: int, tier_bps: int) -> bool:
    """Return whether base_bps, qty and tier_bps are nonnegative."""
    return base_bps >= 0 and qty >= 0 and tier_bps >= 0


def my_slippage_charge(base_bps: int, qty: int, tier_bps: int):
    """Return the base charge plus quantity times the per-unit tier charge, in basis points. Raise
    AssertionError if the input predicate rejects the arguments.
    """
    assert pre_condition(base_bps, qty, tier_bps), "pre violated"
    return base_bps + qty * tier_bps


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(1, 10, 2) == 21
    assert candidate(0, 0, 5) == 0
    assert candidate(3, 4, 0) == 3
    assert candidate(2, 5, 1) == 7
    assert candidate(1, 0, 2) == 1
    return True


if __name__ == "__main__":
    assert check(my_slippage_charge)
    print(f"All tests passed: {__file__}!")
