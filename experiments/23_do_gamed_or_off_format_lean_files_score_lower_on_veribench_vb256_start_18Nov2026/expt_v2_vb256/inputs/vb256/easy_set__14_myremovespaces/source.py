"""Remove every literal ASCII space character from a string, preserving all other characters. Empty
input and input containing only ASCII spaces return an empty string. Non-string input raises
ValueError.
"""

def pre(s: str) -> bool:
    """True iff the input is a string."""
    return isinstance(s, str)

def prog(s: str) -> str:
    """Return s with every literal ASCII space (' ') removed. Preserve all other characters. Raise
    ValueError for non-string input.
    """
    if not pre(s):
        raise ValueError(f"Require string input (got s={s!r})")
    return s.replace(' ', '')

# -- Tests --

from typing import Callable

def check(candidate: Callable[[str], str]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate('hello world') == 'helloworld'
    assert candidate('') == ''
    try:
        candidate(None)
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
