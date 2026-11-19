"""Compare two byte strings for equality using early-exit logic."""


def unsafe_timing_compare(expected: bytes, actual: bytes) -> bool:
    """Return whether two byte strings are equal. Return False for unequal lengths or at the first
    mismatching byte. Otherwise return True, including for two empty byte strings. This
    comparison uses early exits and is not a constant-time comparison.
    """
    if len(expected) != len(actual):
        return False
    for e, a in zip(expected, actual):
        if e != a:
            return False
    return True


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(b'secret', b'secret') is True
    assert candidate(b'secret', b'Xecret') is False
    assert candidate(b'secret', b'secrex') is False
    assert candidate(b'abc', b'ab') is False
    assert candidate(b'ab', b'abc') is False
    return True


assert check(unsafe_timing_compare), "Candidate failed timing comparison tests"
print("All tests passed.")
