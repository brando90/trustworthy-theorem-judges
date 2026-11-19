# Synthetic VeriBench task - Inspired by: financial exchange and clearing-house invariants
# Original language: Python
# Category: finance
# Lines: 36
"""Return the quantity that can be matched from the submitted buy and sell quantities."""

from typing import Callable


def pre_condition(buy_qty: int, sell_qty: int) -> bool:
    """Return whether buy_qty and sell_qty are nonnegative."""
    return buy_qty >= 0 and sell_qty >= 0


def my_auction_fill_qty(buy_qty: int, sell_qty: int):
    """Return the smaller of buy_qty and sell_qty. Raise AssertionError if either quantity is
    negative.
    """
    assert pre_condition(buy_qty, sell_qty), "pre violated"
    return buy_qty if buy_qty <= sell_qty else sell_qty


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(10, 3) == 3
    assert candidate(3, 10) == 3
    assert candidate(5, 5) == 5
    assert candidate(0, 7) == 0
    assert candidate(0, 3) == 0
    return True


if __name__ == "__main__":
    assert check(my_auction_fill_qty)
    print(f"All tests passed: {__file__}!")
