"""
Provides a function for shell-escaping a string.

Sourced from Python's standard `shlex` library.
"""

from typing import Callable, Any

# -- Pre-condition --

def pre_quote(s: Any) -> bool:
    """True iff input is a string."""
    return isinstance(s, str)

# -- Implementation --

def quote(s):
    """Return two single quotes for any falsy input. Otherwise require a string, raising TypeError
    for other types. Leave strings containing only ASCII letters, digits, or _@%+=:,./-
    unchanged. Single-quote other strings, escaping embedded single quotes for a POSIX shell
    argument.
    """
    if not s:
        return "''"

    if not isinstance(s, str):
        raise TypeError("expected string object")

    # Safe characters for POSIX shells
    safe_chars = set('abcdefghijklmnopqrstuvwxyz'
                     'ABCDEFGHIJKLMNOPQRSTUVWXYZ'
                     '0123456789'
                     '_@%+=:,./-')
                     
    # Check if all chars are safe
    if all(c in safe_chars for c in s):
        return s

    # Use single quotes, and replace single quotes with '"'"'
    return "'" + s.replace("'", "'\"'\"'") + "'"

# Main function to be verified
def benchmark_quote(s):
    """Return s quoted as one POSIX shell argument: empty strings become two single quotes, strings
    containing only ASCII letters, digits, or _@%+=:,./- remain unchanged, and other strings are
    single-quoted with embedded single quotes escaped. Raise TypeError for nonstrings.
    """
    if not pre_quote(s):
        # Allow the implementation to raise the TypeError if it's not a string
        if not isinstance(s, str):
             raise TypeError("expected string object")
    return quote(s)

# -- Tests --

def check(quote_cand: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert quote_cand('') == "''"
    assert quote_cand('abc') == 'abc'
    assert quote_cand('a b c') == "'a b c'"
    assert quote_cand("a'b") == '\'a\'"\'"\'b\''
    assert quote_cand('a') == 'a'
    return True

if __name__ == "__main__":
    assert check(benchmark_quote), f"Failed: {__file__}"
    print("All tests passed.")
