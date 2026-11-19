# Synthetic VeriBench task — Inspired by: RFC 7231 §6 (HTTP status code classes)
# Original language: Python
# Category: 02_rfc (internet RFCs)
# Lines: ~75
"""Return the HTTP status-class digit for any integer from 100 through 599, without checking
whether the code is assigned.
"""

from typing import Callable


def pre_condition(code: int) -> bool:
    """Return True iff code is between 100 and 599 inclusive. Assignment as an HTTP status code is
    not checked.
    """
    return 100 <= code <= 599


def my_http_status_class(code: int) -> int:
    """Return code // 100 for any integer in [100, 599], including unassigned HTTP status codes.
    Edge cases: - code = 100 → class 1 (Informational) - code = 599 → class 5 (Server Error) -
    codes outside [100, 599] violate the precondition. Raise AssertionError when pre_condition
    rejects the arguments.
    """
    assert pre_condition(code), "RFC 7231: status code outside [100, 599]"
    return code // 100


def check(candidate: Callable[[int], int]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(100) == 1
    assert candidate(200) == 2
    assert candidate(301) == 3
    assert candidate(404) == 4
    try:
        candidate(0)
    except AssertionError:
        pass
    else:
        raise AssertionError('expected AssertionError')
    return True


if __name__ == "__main__":
    assert check(my_http_status_class)
    print(f"All tests passed: {__file__}!")
