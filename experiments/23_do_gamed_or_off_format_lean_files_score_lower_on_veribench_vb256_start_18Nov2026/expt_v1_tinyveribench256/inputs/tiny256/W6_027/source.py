"""Model a check/use mismatch with supplied lengths: return len2 when len1 <= buf_size, otherwise
None. No library reads occur.
"""


def unsafe_double_read(len1: int, len2: int, buf_size: int):
    """Return len2 unchanged if len1 <= buf_size. Otherwise return None. No lower bound is checked,
    and len2 is not validated. The arguments represent two readings. The function performs no
    reads itself.
    """
    if len1 <= buf_size:
        return len2  # second read — may differ from checked len1!
    return None


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(5, 5, 100) == 5
    assert candidate(5, 999, 100) == 999
    assert candidate(200, 200, 100) is None
    assert candidate(100, 100, 100) == 100
    assert candidate(50, 0, 100) == 0
    return True


assert check(unsafe_double_read), "Candidate failed tests"
print("All tests passed.")
