# Synthetic VeriBench task — Inspired by: aerospace flight command execution window
# Original language: Python
# Category: 04_aerospace
# Lines: ~70
"""Check whether a supplied mission time lies within an inclusive interval specified in milliseconds."""

from typing import Callable


def pre_condition(nowMs, openMs, closeMs) -> bool:
    """Pre: all mission-time fields are non-negative integer milliseconds."""
    return all(isinstance(x, int) and x >= 0 for x in [nowMs, openMs, closeMs])


def my_command_window(nowMs, openMs, closeMs) -> bool:
    """Return True exactly when openMs <= nowMs <= closeMs, including both endpoints. Reversed
    bounds return False. This only compares supplied times. It does not execute or authorize
    commands. Raise AssertionError unless all inputs are non-negative Python integers, including
    bool.
    """
    assert pre_condition(nowMs, openMs, closeMs), "mission-time fields must be non-negative integers"
    return (openMs <= nowMs) and (nowMs <= closeMs)


def check(candidate: Callable[..., bool]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(50, 40, 60) is True
    assert candidate(39, 40, 60) is False
    assert candidate(61, 40, 60) is False
    assert candidate(60, 40, 60) is True
    assert candidate(0, 0, 0) is True
    return True


if __name__ == "__main__":
    assert check(my_command_window)
    print(f"All tests passed: {__file__}!")
