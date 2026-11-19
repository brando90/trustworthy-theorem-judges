# Synthetic VeriBench task -- Inspired by: models revoked pointer-capability use rejection.
# Original language: Python
# Category: memory_bugs
"""Return whether a capability is issued (1) and has not been revoked (0)."""

from typing import Callable


def pre_condition(issued, revoked) -> bool:
    """Return whether issued and revoked are nonnegative integers and issued is one of 0, 1 and
    revoked is one of 0, 1.
    """
    return isinstance(issued, int) and issued >= 0 and isinstance(revoked, int) and revoked >= 0 and issued in (0, 1) and revoked in (0, 1)


def my_capability_use_allowed(issued, revoked) -> bool:
    """Return whether a capability is issued (1) and has not been revoked (0). Raise AssertionError
    if the input predicate rejects the arguments.
    """
    assert pre_condition(issued, revoked), "pre violated"
    return issued == 1 and revoked == 0


def _must_raise_assertion(thunk: Callable[[], object]) -> None:
    """Return normally iff thunk() raises AssertionError; otherwise raise AssertionError."""
    try:
        thunk()
    except AssertionError:
        return
    raise AssertionError("expected AssertionError")


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(1, 0) is True
    assert candidate(1, 1) is False
    assert candidate(0, 0) is False
    _must_raise_assertion(lambda: candidate(-1, 0))
    assert candidate(0, 1) is False
    return True


if __name__ == "__main__":
    assert check(my_capability_use_allowed)
    print(f"All tests passed: {__file__}!")
