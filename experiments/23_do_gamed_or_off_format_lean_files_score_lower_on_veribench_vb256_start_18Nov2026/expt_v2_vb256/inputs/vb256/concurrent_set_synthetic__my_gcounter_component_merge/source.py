# Synthetic VeriBench task — Inspired by: G-Counter CRDT componentwise max merge
# Original language: Python
# Category: 10_concurrent
"""G-Counter component merge that keeps the larger replica count."""

from typing import Callable


def pre_condition(left: int, right: int) -> bool:
    """Return whether left and right are nonnegative."""
    return left >= 0 and right >= 0


def my_gcounter_component_merge(left: int, right: int):
    """Return the larger of left and right for a single G-Counter component, choosing left when
    equal. Raise AssertionError if either input is negative. This computes a value without
    updating replica state.
    """
    assert pre_condition(left, right), "pre violated"
    return left if left >= right else right


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(7, 2) == 7
    assert candidate(4, 4) == 4
    assert candidate(0, 0) == 0
    try:
        candidate(-1, 0)
    except AssertionError:
        pass
    else:
        raise AssertionError('expected AssertionError')
    assert candidate(3, 5) == 5
    return True


if __name__ == "__main__":
    assert check(my_gcounter_component_merge)
    print(f"All tests passed: {__file__}!")
