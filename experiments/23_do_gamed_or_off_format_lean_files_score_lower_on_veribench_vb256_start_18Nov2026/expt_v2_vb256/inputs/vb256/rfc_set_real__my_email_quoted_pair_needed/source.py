# Source: https://github.com/python/cpython, Lib/email/_parseaddr.py, commit 24c4aecc1674414d3dc3238625802778c4ad29d2, PSF-License
# Original language: Python
# Category: rfc
"""Return True iff c is double quote or backslash, the characters CPython escapes in an RFC email
quoted string.
"""

from typing import Callable


def my_email_quoted_pair_needed(c: int) -> bool:
    """Return True iff c is ASCII double quote (34) or backslash (92), the characters CPython
    backslash-escapes in an email quoted string. Return False for other ASCII codes. Raise
    AssertionError unless 0 ≤ c ≤ 127.
    """
    assert 0 <= c <= 127, "pre violated"
    return c in (34, 92)


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(34) is True
    assert candidate(92) is True
    assert candidate(65) is False
    assert candidate(32) is False
    assert candidate(64) is False
    return True


if __name__ == "__main__":
    assert check(my_email_quoted_pair_needed)
    print(f"All tests passed: {__file__}!")
