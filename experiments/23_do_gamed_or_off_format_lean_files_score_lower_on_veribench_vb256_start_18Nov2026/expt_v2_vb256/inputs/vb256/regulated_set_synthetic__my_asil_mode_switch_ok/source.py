# Synthetic VeriBench task -- Inspired by: ASIL-Aware Mode Switch Authorization (ISO 26262)
# Original language: Python
# Category: 05_regulated
"""Synthetic mode-switch predicate comparing nonnegative authority and required levels with a
supplied lock flag. Return a Boolean. Negative levels raise AssertionError.
"""

from typing import Callable


def pre_condition(authority: int, required_asil: int, locked: bool) -> bool:
    """Return whether authority and required_asil are nonnegative."""
    return authority >= 0 and required_asil >= 0


def my_asil_mode_switch_ok(authority: int, required_asil: int, locked: bool) -> bool:
    """Return whether the authority level is sufficient for the requested safety mode and the mode
    is unlocked.

    The input check requires that authority and required_asil are nonnegative. A failed check
    raises AssertionError.
    """
    assert pre_condition(authority, required_asil, locked), "pre violated"
    return bool(required_asil <= authority and not locked)


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(4, 3, False) is True
    assert candidate(3, 3, False) is True
    assert candidate(1, 3, False) is False
    assert candidate(4, 3, True) is False
    try:
        candidate(-1, 0, False)
    except AssertionError:
        pass
    else:
        raise AssertionError('expected AssertionError')
    return True


if __name__ == "__main__":
    assert check(my_asil_mode_switch_ok)
    print(f"All tests passed: {__file__}!")
