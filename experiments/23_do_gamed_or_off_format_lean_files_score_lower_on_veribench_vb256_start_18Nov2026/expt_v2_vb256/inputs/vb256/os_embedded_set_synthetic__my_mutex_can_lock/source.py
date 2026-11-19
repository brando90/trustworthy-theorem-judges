# Synthetic VeriBench task - Inspired by: single-owner non-recursive mutex acquisition guard
# Original language: Python
# Category: os_embedded
"""Return whether an unowned mutex (owner 0) can be acquired by the given positive thread ID."""
from typing import Callable
def pre_condition(owner: int, tid: int) -> bool:
    """Return whether owner and tid are nonnegative."""
    return owner >= 0 and tid >= 0
def my_mutex_can_lock(owner: int, tid: int) -> bool:
    """Return whether an unowned mutex (owner 0) can be acquired by the given positive thread ID.
    Raise AssertionError if the input predicate rejects the arguments.

    The input check requires that owner and tid are nonnegative. A failed check raises
    AssertionError.
    """
    assert pre_condition(owner, tid), "pre violated"
    return bool(owner == 0 and tid > 0)
def _must_raise(call) -> None:
    """Return normally iff call() raises AssertionError; otherwise raise AssertionError."""
    try:
        call()
    except AssertionError:
        return
    raise AssertionError("expected precondition failure")
def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(0, 1) is True
    assert candidate(0, 7) is True
    assert candidate(2, 1) is False
    assert candidate(2, 2) is False
    _must_raise(lambda: candidate(-1, 1))
    return True

if __name__ == "__main__":
    assert check(my_mutex_can_lock)
    print(f"All tests passed: {__file__}!")
