# Source: https://github.com/openaps/oref0, lib/profile/targets.js, 88cf032aa74ff25f69464a7d9cd601ee3940c0b3, MIT
# Original language: JavaScript-port
# Category: medical_oss
"""Return whether the temporary target remains active. Cancellation disables it, and its age must
be strictly below a positive duration in minutes.
"""

def my_temp_target_active(age_min, duration_min, cancel) -> bool:
    """Return True when cancel is the Boolean False, duration_min is positive and age_min is less
    than duration_min. An integer zero does not satisfy the Boolean identity check. Raise
    AssertionError if an input is neither a Boolean nor an integer.
    """
    assert all(isinstance(x, bool) or isinstance(x, int) for x in [age_min, duration_min, cancel]), "inputs must be bool/int scalars"
    return bool(cancel is False and duration_min > 0 and age_min < duration_min)

def pre_condition(age_min, duration_min, cancel) -> bool:
    """Return whether age_min, duration_min and cancel are integers."""
    return all(isinstance(x, bool) or isinstance(x, int) for x in [age_min, duration_min, cancel])

from typing import Callable

def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(10, 30, False) is True
    assert candidate(10, 30, True) is False
    assert candidate(30, 30, False) is False
    try:
        candidate('bad', 0, 0)
    except (AssertionError, TypeError):
        pass
    else:
        raise AssertionError('expected (AssertionError, TypeError)')
    assert candidate(0, 30, False) is True
    return True

if __name__ == "__main__":
    assert check(my_temp_target_active)
    print(f"All tests passed: {__file__}!")
