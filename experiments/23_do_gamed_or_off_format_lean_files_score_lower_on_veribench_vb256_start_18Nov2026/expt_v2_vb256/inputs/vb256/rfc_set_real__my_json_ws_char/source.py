# Source: https://github.com/python/cpython, Lib/json/decoder.py, commit 24c4aecc1674414d3dc3238625802778c4ad29d2, PSF-License
# Original language: Python
# Category: rfc
"""Return True iff c is one of JSON whitespace space, tab, LF, or CR."""

from typing import Callable


def my_json_ws_char(c: int) -> bool:
    """Return True iff c is one of JSON whitespace space, tab, LF, or CR. Used e.g. to skip
    insignificant whitespace between tokens while parsing JSON.

    Raise AssertionError unless 0 ≤ c ≤ 127.
    """
    assert 0 <= c <= 127, "pre violated"
    return c in (32,9,10,13)



def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(32) is True
    assert candidate(9) is True
    assert candidate(10) is True
    assert candidate(13) is True
    assert candidate(65) is False
    return True


if __name__ == "__main__":
    assert check(my_json_ws_char)
    print(f"All tests passed: {__file__}!")
