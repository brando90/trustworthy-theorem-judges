# Source: https://github.com/python/cpython, Lib/base64.py, 24c4aecc1674414d3dc3238625802778c4ad29d2, PSF-License
# Original language: Python
# Category: crypto
# Lines: 59
"""Compute the Base64url padding characters needed for a byte length."""

from typing import Callable


def pre_condition(byte_len: int) -> bool:
    """Return True exactly when byte_len is a non-negative Python int, including bool. Otherwise
    return False.
    """
    return isinstance(byte_len, int) and byte_len >= 0


def my_base64url_padding_len(byte_len: int) -> int:
    """Return the number of '=' padding characters for Base64url encoding. Used e.g. to compute how
    many padding characters Base64url encoding adds for a given number of bytes or to predict
    the padded length of an encoded token.

    Raise AssertionError when pre_condition rejects the arguments.
    """
    assert pre_condition(byte_len), "pre violated"
    rem = byte_len % 3
    if rem == 0:
        return 0
    if rem == 1:
        return 2
    return 1


def check(candidate: Callable[[int], int]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(0) == 0
    assert candidate(1) == 2
    assert candidate(2) == 1
    assert candidate(3) == 0
    assert candidate(4) == 2
    return True


if __name__ == "__main__":
    assert check(my_base64url_padding_len)
    print(f"All tests passed: {__file__}!")
