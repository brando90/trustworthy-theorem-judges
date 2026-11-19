"""Return the number of characters in a string.

Edge cases:
- Empty string has length 0.
- The function raises ValueError if input is not a string.
"""

def pre(s: str) -> bool:
    """True iff the input is a string."""
    return isinstance(s, str)

def prog(s: str) -> int:
    """Return the number of Unicode code points in s, including zero for an empty string. Raise
    ValueError if s is not a string.
    """
    if not pre(s):
        raise ValueError(f"Require string input (got s={s!r})")
    return len(s)

# -- Tests --

from typing import Callable

def check(candidate: Callable[[str], int]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate('hello') == 5
    assert candidate('') == 0
    try:
        candidate(None)
    except ValueError:
        pass
    else:
        raise AssertionError('expected ValueError')
    assert candidate('h') == 1
    assert candidate('ab') == 2
    return True

if __name__ == "__main__":
    assert check(prog), f"Failed: {__file__}"
    print("All tests passed.")
