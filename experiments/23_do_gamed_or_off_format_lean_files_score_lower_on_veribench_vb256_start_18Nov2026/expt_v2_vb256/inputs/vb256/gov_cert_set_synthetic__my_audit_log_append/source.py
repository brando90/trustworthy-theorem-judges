# Synthetic VeriBench task — Inspired by: NIST SP 800-92 audit logging
# Original language: Python
# Category: 13_gov_cert
# Lines: ~50
"""Compute the length after a hypothetical single-event append. No log is accessed or modified."""

from typing import Callable


def pre_condition(current_length: int) -> bool:
    """Pre: length is non-negative."""
    return current_length >= 0


def my_audit_log_append(current_length: int) -> int:
    """Return current_length + 1 without accessing or modifying a log. Raise AssertionError if
    current_length is negative.
    """
    assert pre_condition(current_length), "negative log length"
    return current_length + 1


def check(candidate: Callable[[int], int]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(0) == 1
    assert candidate(5) == 6
    assert candidate(100) == 101
    assert candidate(2147483647) == 2147483648
    try:
        candidate(-1)
    except AssertionError:
        pass
    else:
        raise AssertionError('expected AssertionError')
    return True


if __name__ == "__main__":
    assert check(my_audit_log_append)
    print(f"All tests passed: {__file__}!")
