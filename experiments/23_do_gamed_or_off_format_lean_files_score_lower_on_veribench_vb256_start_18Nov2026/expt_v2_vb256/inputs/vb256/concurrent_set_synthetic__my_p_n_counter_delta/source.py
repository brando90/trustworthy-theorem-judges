# Synthetic VeriBench task - Inspired by: PN-Counter delta merge
# Original language: Python
# Category: concurrent
"""Synthetic counter arithmetic returning increments minus decrements when decrements does not
exceed increments.
"""
from typing import Callable
def pre_condition(increments: int, decrements: int) -> bool:
    """Return whether decrements <= increments. Neither argument is required to be nonnegative."""
    return decrements <= increments
def my_p_n_counter_delta(increments: int, decrements: int) -> int:
    """Return increments - decrements. Raise AssertionError if decrements > increments. Negative
    arguments are accepted when they satisfy the comparison.
    """
    assert pre_condition(increments, decrements), "pre violated"
    return increments - decrements if decrements <= increments else 0
def _must_raise(call) -> None:
    """Call call() and return None if it raises AssertionError. Raise AssertionError if it returns
    normally. Propagate other exceptions.
    """
    try:
        call()
    except AssertionError:
        return
    raise AssertionError("expected precondition failure")
def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(10, 3) == 7
    assert candidate(5, 5) == 0
    assert candidate(8, 0) == 8
    assert candidate(0, 0) == 0
    _must_raise(lambda: candidate(3, 7))
    return True

if __name__ == "__main__":
    assert check(my_p_n_counter_delta)
    print(f"All tests passed: {__file__}!")
