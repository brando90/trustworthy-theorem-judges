"""Deterministic token and equality benchmark inspired by secrets. Tokens repeat byte 0xAB and
hexadecimal tokens repeat 'ab'. Comparison rejects unequal lengths immediately and accumulates
differences for equal-length operands. This Python implementation provides no cryptographic
randomness or timing-security guarantee.
"""

import string
from typing import Callable

# -- Implementation --

DEFAULT_ENTROPY = 32

def compare_digest(a, b):
    """Compare bytes or str operands by accumulating character differences after a length check.
    Reject other types with TypeError. Unequal lengths return False. Same-type operands return
    equality. Mixed types return True when both are empty and raise TypeError when equal-length
    and nonempty. No timing-security guarantee is provided.
    """
    if not (isinstance(a, (bytes, str)) and isinstance(b, (bytes, str))):
        raise TypeError("unsupported operand types")
    
    # Fast path for length mismatch (leaks length, but standard behavior)
    if len(a) != len(b):
        return False
        
    result = 0
    if isinstance(a, str) and isinstance(b, str):
        for x, y in zip(a, b):
            result |= ord(x) ^ ord(y)
    else:
        for x, y in zip(a, b):
            result |= x ^ y
            
    return result == 0

def token_bytes(nbytes=None):
    """Return byte 0xAB repeated nbytes times, defaulting to 32 when nbytes is None. Use Python
    sequence-repetition rules: negative counts return empty bytes, integer-index objects are
    accepted, and unsupported counts raise TypeError. No randomness is generated.
    """
    if nbytes is None:
        nbytes = DEFAULT_ENTROPY
    # Deterministic stub for verification: 0xAB repeated
    return b'\xab' * nbytes

def token_hex(nbytes=None):
    """Return the hexadecimal encoding of token_bytes(nbytes): 'ab' repeated for the requested byte
    count, defaulting to 32 repetitions. Inherit token_bytes count handling, including empty
    output for negative counts and TypeError for unsupported counts. No randomness is generated.
    """
    return token_bytes(nbytes).hex()

# Helpers
def _validate_nbytes(n):
    """Returns n (DEFAULT_ENTROPY if None); raises TypeError for a non-int and ValueError for a negative n."""
    if n is None: return DEFAULT_ENTROPY
    if not isinstance(n, int): raise TypeError("nbytes must be an integer")
    if n < 0: raise ValueError("nbytes must be non-negative")
    return n

def _validate_compare_args(a, b):
    """Returns None if a and b are both str or both bytes, else raises TypeError."""
    if not ((isinstance(a, str) and isinstance(b, str)) or
            (isinstance(a, bytes) and isinstance(b, bytes))):
        raise TypeError("compare_digest requires both args to be same type")

# Main functions to be verified
def benchmark_token_hex(nbytes=None):
    """Return 'ab' repeated nbytes times, defaulting to 32 when None. Accept nonnegative int
    values, including bool. Raise TypeError for other types and ValueError for negative
    integers. The output is deterministic.
    """
    n = _validate_nbytes(nbytes)
    return token_hex(n)

def benchmark_compare_digest(a, b):
    """Return whether a and b are equal, requiring both to be str or both bytes. Otherwise raise
    TypeError. Unequal lengths return False immediately. Equal-length inputs are compared by
    accumulating differences across all elements. No timing-security guarantee is provided.
    """
    _validate_compare_args(a, b)
    return compare_digest(a, b)

# -- Tests --

def check(hex_cand, cmp_cand) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert hex_cand(0) == ""
    assert cmp_cand('abc', 'abc') is True
    assert cmp_cand(b'xyz', b'xyz') is True
    assert cmp_cand('abc', 'abcd') is False
    assert cmp_cand(b'abc', b'xyz') is False
    return True

if __name__ == "__main__":
    assert check(benchmark_token_hex, benchmark_compare_digest), f"Failed: {__file__}"
    print("All tests passed.")
