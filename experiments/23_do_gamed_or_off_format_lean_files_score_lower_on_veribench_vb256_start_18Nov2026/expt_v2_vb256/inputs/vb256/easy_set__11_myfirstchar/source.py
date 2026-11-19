"""Return the first character of a non-empty string.

Edge cases:
- Single character strings return that character.
- The function raises ValueError if the string is empty or not a string.
"""

def pre(s: str) -> bool:
    """True iff the input is a non-empty string."""
    return isinstance(s, str) and len(s) > 0

def prog(s: str) -> str:
    """
    Return the first character of s for non-empty strings.
    Raises ValueError if the precondition is violated.

    Used e.g. to take the initial letter of a name for alphabetical bucketing or to build a person's initials.
    """
    if not pre(s):
        raise ValueError(f"Require non-empty string (got s={s!r})")
    return s[0]

# -- Tests --

from typing import Callable

def check(candidate: Callable[[str], str]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate('hello') == 'h'
    assert candidate('A') == 'A'
    try:
        candidate('')
    except ValueError:
        pass
    else:
        raise AssertionError('expected ValueError')
    assert candidate('h') == 'h'
    assert candidate('a') == 'a'
    return True

if __name__ == "__main__":
    assert check(prog), f"Failed: {__file__}"
    print("All tests passed.")
