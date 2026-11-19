# Synthetic VeriBench task — Inspired by: NIST SP 800-53 ABAC deny-by-default
# Original language: Python
# Category: 13_gov_cert
# Lines: ~65
"""Combine three supplied Boolean decision flags, returning True only when all three are True.
Non-Boolean inputs raise AssertionError.
"""

from typing import Callable
import itertools


def pre_condition(authenticated: bool, clearance_ok: bool, purpose_allowed: bool) -> bool:
    """Pre: all certification decision inputs are booleans."""
    return isinstance(authenticated, bool) and isinstance(clearance_ok, bool) and isinstance(purpose_allowed, bool)


def my_abac_deny_default(authenticated: bool, clearance_ok: bool, purpose_allowed: bool) -> bool:
    """Return True only when authenticated, clearance_ok, and purpose_allowed are all True.
    Otherwise return False for valid Boolean inputs. These flags are supplied decisions. Raise
    AssertionError if any input is not Boolean.
    """
    assert pre_condition(authenticated, clearance_ok, purpose_allowed), "decision inputs must be booleans"
    return authenticated and clearance_ok and purpose_allowed


def check(candidate: Callable[..., bool]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(True, True, True) is True
    assert candidate(False, True, True) is False
    assert candidate(True, False, True) is False
    assert candidate(True, True, False) is False
    try:
        candidate('bad', True, True)
    except AssertionError:
        pass
    else:
        raise AssertionError('expected AssertionError')
    return True


if __name__ == "__main__":
    assert check(my_abac_deny_default)
    print(f"All tests passed: {__file__}!")
