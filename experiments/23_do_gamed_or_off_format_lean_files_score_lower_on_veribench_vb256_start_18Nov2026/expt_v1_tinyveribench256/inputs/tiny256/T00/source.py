"""Remove all digit characters from a string.

Edge cases:
- Empty string returns empty string.
- Non-string input is invalid and raises ValueError.
"""

def pre(s: str) -> bool:
    """True iff s is a string."""
    return isinstance(s, str)

def remove_digits(s: str) -> str:
    """Return a string containing, in order, the input characters for which str.isdigit() is False.
    Preserve all other characters, including punctuation and whitespace. Empty input returns an
    empty string. Raise ValueError for non-string input.
    """
    if not pre(s):
        raise ValueError("Input must be a string")
    return ''.join(c for c in s if not c.isdigit())

# -- Tests --
from typing import Callable

def check(candidate: Callable[[str], str]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate('abc123def') == 'abcdef'
    assert candidate('') == ''
    try:
        candidate(None)
    except ValueError:
        pass
    else:
        raise AssertionError('expected ValueError')
    assert candidate('a') == 'a'
    assert candidate('ab') == 'ab'
    return True

if __name__ == "__main__":
    assert check(remove_digits), f"Failed: {__file__}"
    print("All tests passed.")
