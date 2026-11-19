"""Checks whether a non-negative integer reads the same forwards and backwards."""

from typing import Callable

def pre(n: int) -> bool:
    """Return True for nonnegative Python integers, including booleans. Return False otherwise."""
    return isinstance(n, int) and n >= 0

def is_palindrome(n: int) -> bool:
    """Return whether the decimal digits of a nonnegative integer read identically backwards.
    Boolean inputs are accepted and return True. Raise ValueError for negative integers or
    inputs that are not Python integers.
    """
    if not pre(n):
        raise ValueError("Input must be non-negative integer")
    if n < 10:
        return True
    digits = str(n)
    return digits == digits[::-1]

def check(candidate: Callable[[int], bool]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(121) is True
    assert candidate(0) is True
    assert candidate(10) is False
    try:
        candidate(-1)
    except ValueError:
        pass
    else:
        raise AssertionError('expected ValueError')
    assert candidate(1) is True
    return True

if __name__ == "__main__":
    assert check(is_palindrome), f"Failed: {__file__}"
    print("All tests passed.")
