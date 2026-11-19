# Synthetic VeriBench task — Inspired by: FIPS-style fixed-point deterministic rounding
# Original language: Python
# Category: 13_gov_cert
# Lines: ~65
"""Round whole cents to an even cent when a supplied nonzero flag indicates an exact half-cent tie."""

from typing import Callable


def pre_condition(whole_cents: int, half_flag: int) -> bool:
    """Return whether whole_cents and half_flag each lie in [0, 1_000_000]. This predicate checks
    comparisons only, without enforcing integer types.
    """
    return 0 <= whole_cents <= 1_000_000 and 0 <= half_flag <= 1_000_000


def my_round_half_even_cents(whole_cents: int, half_flag: int) -> int:
    """Raise AssertionError unless pre_condition accepts both arguments. Return whole_cents
    unchanged when half_flag is zero or whole_cents is even. Otherwise return whole_cents + 1.
    Every nonzero admissible half_flag indicates a half-cent tie.
    """
    assert pre_condition(whole_cents, half_flag), "counter inputs out of range"
    return whole_cents if (not half_flag or whole_cents % 2 == 0) else whole_cents + 1


def check(candidate: Callable[[int, int], int]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(0, 0) == 0
    assert candidate(10, 3) == 10
    assert candidate(7, 9) == 8
    assert candidate(7, 0) == 7
    assert candidate(1, 0) == 1
    return True


if __name__ == "__main__":
    assert check(my_round_half_even_cents)
    print(f"All tests passed: {__file__}!")
