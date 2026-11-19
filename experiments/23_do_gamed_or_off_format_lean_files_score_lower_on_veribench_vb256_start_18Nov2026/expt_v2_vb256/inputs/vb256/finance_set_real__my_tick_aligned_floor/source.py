# Source: https://github.com/pmorissette/ffn, ffn/core.py, commit 8e6f84770fb92cdd0f84403bbaa74b21dc690d0b, MIT
# Original language: Python
# Category: finance
# Lines: 38
"""ffn-Style Tick-Aligned Price Floor"""

from typing import Callable


def pre_condition(price: int, tick: int) -> bool:
    """Return whether tick is positive and price is nonnegative."""
    return price >= 0 and tick > 0


def my_tick_aligned_floor(price: int, tick: int):
    """For positive tick, return the largest multiple of tick not exceeding price. Return zero when
    tick is zero. Raise AssertionError if price or tick is negative. This function accepts zero
    tick even though pre_condition returns False for it.
    """
    assert price >= 0 and tick >= 0, "pre violated"
    if tick == 0:
        return 0
    return (price // tick) * tick


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(105, 5) == 105
    assert candidate(10, 0) == 0
    assert candidate(7, 1) == 7
    assert candidate(100, 25) == 100
    assert candidate(99, 25) == 75
    return True


if __name__ == "__main__":
    assert check(my_tick_aligned_floor)
    print(f"All tests passed: {__file__}!")
