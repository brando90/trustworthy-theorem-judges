# Synthetic VeriBench task -- Inspired by: Airspeed Envelope Command Acceptance (DO-178C DAL)
# Original language: Python
# Category: 05_regulated
"""Synthetic airspeed interval predicate. Return whether speed lies within supplied inclusive
limits. Negative speed or minimum, or reversed limits, raise AssertionError.
"""

from typing import Callable


def pre_condition(speed: int, v_min: int, v_max: int) -> bool:
    """Return whether speed and v_min are nonnegative and v_max ≥ v_min."""
    return speed >= 0 and v_min >= 0 and v_max >= v_min


def my_airspeed_envelope_accept(speed: int, v_min: int, v_max: int) -> bool:
    """Return whether the measured airspeed is within the inclusive minimum and maximum limits.
    Raise AssertionError if the input predicate rejects the arguments.

    The input check requires that speed and v_min are nonnegative and v_max ≥ v_min. A failed
    check raises AssertionError.
    """
    assert pre_condition(speed, v_min, v_max), "pre violated"
    return bool(v_min <= speed <= v_max)


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(150, 100, 250) is True
    assert candidate(100, 100, 250) is True
    assert candidate(250, 100, 250) is True
    assert candidate(80, 100, 250) is False
    try:
        candidate(1, 10, 5)
    except AssertionError:
        pass
    else:
        raise AssertionError('expected AssertionError')
    return True


if __name__ == "__main__":
    assert check(my_airspeed_envelope_accept)
    print(f"All tests passed: {__file__}!")
