# Synthetic VeriBench task -- Inspired by: Audit Log Append Authorization Gate (FDA 21 CFR 820)
# Original language: Python
# Category: 05_regulated
"""Synthetic audit-append eligibility predicate using two nonnegative timestamps and a supplied
operator flag. It returns a Boolean without modifying a log. Negative timestamps raise
AssertionError.
"""

from typing import Callable


def pre_condition(last_ts: int, new_ts: int, operator_ok: bool) -> bool:
    """Return whether last_ts and new_ts are nonnegative."""
    return last_ts >= 0 and new_ts >= 0


def my_audit_append_authorized(last_ts: int, new_ts: int, operator_ok: bool) -> bool:
    """Return whether new_ts is strictly greater than last_ts and the supplied operator_ok flag is
    true. Raise AssertionError if either timestamp is negative.
    """
    assert pre_condition(last_ts, new_ts, operator_ok), "pre violated"
    return bool(last_ts < new_ts and operator_ok)


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(10, 11, True) is True
    assert candidate(0, 1, True) is True
    assert candidate(10, 10, True) is False
    assert candidate(10, 11, False) is False
    try:
        candidate(-1, 0, True)
    except AssertionError:
        pass
    else:
        raise AssertionError('expected AssertionError')
    return True


if __name__ == "__main__":
    assert check(my_audit_append_authorized)
    print(f"All tests passed: {__file__}!")
