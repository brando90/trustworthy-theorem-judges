# Synthetic VeriBench compiler task
# Original language: Python
# Category: 12_compilers
# Lines: ~55
"""Evaluate a Boolean expression in a compiler normalization pass."""

from typing import Callable


def pre_condition(a: bool, b: bool) -> bool:
    """Return whether a and b are Boolean."""
    return isinstance(a, bool) and isinstance(b, bool)


def my_demorgan_and(a: bool, b: bool):
    """Return False when both flags are set and True otherwise. Raise AssertionError for non-Boolean arguments."""
    assert pre_condition(a, b), "pre violated"
    return (not a) or (not b)


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(False, False) == True
    assert candidate(True, True) == False
    assert candidate(False, True) == True
    assert candidate(True, False) == True
    try:
        candidate(None, False)
    except AssertionError:
        pass
    else:
        raise AssertionError("expected AssertionError")
    return True


if __name__ == "__main__":
    assert check(my_demorgan_and)
    print(f"All tests passed: {__file__}!")
