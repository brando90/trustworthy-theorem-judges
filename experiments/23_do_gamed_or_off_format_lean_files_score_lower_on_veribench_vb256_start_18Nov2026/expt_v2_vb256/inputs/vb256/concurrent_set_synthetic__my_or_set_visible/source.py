# Synthetic VeriBench task - Inspired by: observed-remove set add-tag visibility.
# Original language: Python
# Category: 10_concurrent
"""OR-Set visibility check for a unique add tag and its remove tombstone."""

from typing import Callable


def pre_condition(added: bool, removed: bool) -> bool:
    """Return whether added and removed are both bool instances."""
    return isinstance(added, bool) and isinstance(removed, bool)


def my_or_set_visible(added: bool, removed: bool) -> bool:
    """Return True exactly when added is True and removed is False, representing visibility of one
    add tag. Raise AssertionError unless both arguments are bool instances.
    """
    assert pre_condition(added, removed), "pre violated"
    return added and not removed


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(True, False) is True
    assert candidate(True, True) is False
    assert candidate(False, False) is False
    assert candidate(False, True) is False
    try:
        candidate(1, False)
    except AssertionError:
        pass
    else:
        raise AssertionError('expected AssertionError')
    return True


if __name__ == "__main__":
    assert check(my_or_set_visible)
    print(f"All tests passed: {__file__}!")
