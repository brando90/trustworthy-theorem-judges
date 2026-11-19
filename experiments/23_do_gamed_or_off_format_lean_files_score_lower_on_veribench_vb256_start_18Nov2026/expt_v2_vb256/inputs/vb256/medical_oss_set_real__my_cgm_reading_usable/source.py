# Source: https://github.com/openaps/oref0, lib/determine-basal/determine-basal.js, 88cf032aa74ff25f69464a7d9cd601ee3940c0b3, MIT
# Original language: JavaScript-port
# Category: medical_oss
"""Return whether the glucose reading exceeds 10, differs from the sensor-error value 38, has noise
below 3 and is at most five minutes old.
"""

def my_cgm_reading_usable(bg, noise, age_min) -> bool:
    """Return whether the glucose reading exceeds 10, differs from the sensor-error value 38, has
    noise below 3 and is at most five minutes old.

    Raise AssertionError unless bg, noise and age_min are integers.
    """
    assert all(isinstance(x, bool) or isinstance(x, int) for x in [bg, noise, age_min]), "inputs must be bool/int scalars"
    return bool(bg > 10 and bg != 38 and noise < 3 and age_min <= 5)

def pre_condition(bg, noise, age_min) -> bool:
    """Return whether bg, noise and age_min are integers."""
    return all(isinstance(x, bool) or isinstance(x, int) for x in [bg, noise, age_min])

from typing import Callable

def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(100, 0, 5) is True
    assert candidate(100, 3, 5) is False
    try:
        candidate('bad', 0, 0)
    except (AssertionError, TypeError):
        pass
    else:
        raise AssertionError('expected (AssertionError, TypeError)')
    assert candidate(0, 0, 5) is False
    assert candidate(100, 1, 5) is True
    return True

if __name__ == "__main__":
    assert check(my_cgm_reading_usable)
    print(f"All tests passed: {__file__}!")
