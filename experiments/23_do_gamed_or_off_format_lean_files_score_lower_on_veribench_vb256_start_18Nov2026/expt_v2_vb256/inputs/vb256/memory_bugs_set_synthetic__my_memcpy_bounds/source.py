# Synthetic VeriBench task -- Inspired by: models a C memcpy overflow/overread guard.
# Original language: Python
# Category: memory_bugs
"""Return whether both the source and destination have room for an n-byte copy."""

from typing import Callable


def pre_condition(dst_len, src_len, n) -> bool:
    """Return whether dst_len, src_len and n are nonnegative integers."""
    return isinstance(dst_len, int) and dst_len >= 0 and isinstance(src_len, int) and src_len >= 0 and isinstance(n, int) and n >= 0


def my_memcpy_bounds(dst_len, src_len, n) -> bool:
    """Return whether both the source and destination have room for an n-byte copy. Raise
    AssertionError if the input predicate rejects the arguments.
    """
    assert pre_condition(dst_len, src_len, n), "pre violated"
    return n <= dst_len and n <= src_len


def _must_raise_assertion(thunk: Callable[[], object]) -> None:
    """Call thunk once. Return None if it raises AssertionError. Raise AssertionError if it returns
    normally. Other exceptions propagate.
    """
    try:
        thunk()
    except AssertionError:
        return
    raise AssertionError("expected AssertionError")


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(8, 8, 4) is True
    assert candidate(3, 3, 4) is False
    assert candidate(0, 0, 0) is True
    _must_raise_assertion(lambda: candidate(-1, 8, 4))
    assert candidate(8, 8, 0) is True
    return True


if __name__ == "__main__":
    assert check(my_memcpy_bounds)
    print(f"All tests passed: {__file__}!")
