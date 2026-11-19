# Synthetic VeriBench task — Inspired by: counting Bloom filter decrement-on-remove counter cell
# Original language: Python
# Category: 10_concurrent
"""Counting-Bloom-filter cell removal with saturation at zero."""

from typing import Callable


def pre_condition(count: int) -> bool:
    """Return whether count is nonnegative."""
    return count >= 0


def my_bloom_counter_remove(count: int):
    """Return the counter value after a remove operation, never underflowing below zero. Used e.g.
    to delete an item from a counting Bloom filter by decrementing one of its cells without
    underflow or to decrement any counter that must stop at zero.

    The input check requires that count is nonnegative. A failed check raises AssertionError.
    """
    assert pre_condition(count), "pre violated"
    return count - 1 if count > 0 else 0


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(5) == 4
    assert candidate(2) == 1
    assert candidate(100) == 99
    try:
        candidate(-1)
    except AssertionError:
        pass
    else:
        raise AssertionError('expected AssertionError')
    assert candidate(0) == 0
    return True


if __name__ == "__main__":
    assert check(my_bloom_counter_remove)
    print(f"All tests passed: {__file__}!")
