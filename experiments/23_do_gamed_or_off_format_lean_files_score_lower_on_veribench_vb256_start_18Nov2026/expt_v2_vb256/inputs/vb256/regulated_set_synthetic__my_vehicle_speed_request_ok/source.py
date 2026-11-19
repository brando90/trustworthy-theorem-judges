# Synthetic VeriBench task -- Inspired by: Vehicle Speed-Limiter Request Envelope (ISO 26262)
# Original language: Python
# Category: 05_regulated
"""Synthetic speed-request predicate comparing a supplied nonnegative request with two inclusive
nonnegative limits, with a fixed test harness.
"""

from typing import Callable


def pre_condition(desired: int, road_limit: int, system_limit: int) -> bool:
    """Return whether desired, road_limit and system_limit are nonnegative."""
    return desired >= 0 and road_limit >= 0 and system_limit >= 0


def my_vehicle_speed_request_ok(desired: int, road_limit: int, system_limit: int) -> bool:
    """Return whether the requested speed fits both the road and vehicle-system limits. Raise
    AssertionError if the input predicate rejects the arguments.
    """
    assert pre_condition(desired, road_limit, system_limit), "pre violated"
    return bool(desired <= min(road_limit, system_limit))


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(50, 60, 80) is True
    assert candidate(60, 60, 80) is True
    assert candidate(90, 60, 80) is False
    assert candidate(80, 100, 80) is True
    try:
        candidate(-1, 1, 1)
    except AssertionError:
        pass
    else:
        raise AssertionError('expected AssertionError')
    return True


if __name__ == "__main__":
    assert check(my_vehicle_speed_request_ok)
    print(f"All tests passed: {__file__}!")
