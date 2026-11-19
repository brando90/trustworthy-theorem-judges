# Synthetic VeriBench task -- Inspired by: models C union field access guarded by a runtime tag.
# Original language: Python
# Category: memory_bugs
"""Return whether the stored union tag matches the variant requested by the caller."""

from typing import Callable


def pre_condition(actual_tag, expected_tag) -> bool:
    """Return whether actual_tag and expected_tag are nonnegative integers."""
    return isinstance(actual_tag, int) and actual_tag >= 0 and isinstance(expected_tag, int) and expected_tag >= 0


def my_tagged_union_access(actual_tag, expected_tag) -> bool:
    """Return whether the stored union tag matches the variant requested by the caller. Raise
    AssertionError if the input predicate rejects the arguments.
    """
    assert pre_condition(actual_tag, expected_tag), "pre violated"
    return actual_tag == expected_tag


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
    assert candidate(2, 2) is True
    assert candidate(2, 3) is False
    assert candidate(0, 0) is True
    _must_raise_assertion(lambda: candidate(-1, 2))
    assert candidate(0, 2) is False
    return True


if __name__ == "__main__":
    assert check(my_tagged_union_access)
    print(f"All tests passed: {__file__}!")
