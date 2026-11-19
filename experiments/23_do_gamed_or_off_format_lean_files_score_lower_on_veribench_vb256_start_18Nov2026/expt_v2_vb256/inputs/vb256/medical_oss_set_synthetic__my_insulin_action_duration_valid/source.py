# Synthetic VeriBench task -- Inspired by: insulin action duration validity check
# Original language: Python
# Category: medical_oss
"""Return whether the insulin action duration is between three and eight hours, inclusive."""

def my_insulin_action_duration_valid(hours) -> bool:
    """Return whether the insulin action duration is between three and eight hours, inclusive.

    Raise AssertionError unless hours is an integer.
    """
    assert all(isinstance(x, bool) or isinstance(x, int) for x in [hours]), "inputs must be bool/int scalars"
    return bool(3 <= hours and hours <= 8)

def pre_condition(hours) -> bool:
    """Return whether hours is a Python integer, including booleans. No range restriction is imposed."""
    return all(isinstance(x, bool) or isinstance(x, int) for x in [hours])

from typing import Callable

def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(5) is True
    assert candidate(2) is False
    assert candidate(3) is True
    assert candidate(8) is True
    try:
        candidate('bad')
    except (AssertionError, TypeError):
        pass
    else:
        raise AssertionError('expected (AssertionError, TypeError)')
    return True

if __name__ == "__main__":
    assert check(my_insulin_action_duration_valid)
    print(f"All tests passed: {__file__}!")
