"""Always accepts. No replay defence.

Teaching model for MIT 6.858.
"""

def unsafe_accept(_seen: list[int], _new_nonce: int) -> bool:
    """Always accepts.  No replay defence."""
    return True


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate([1, 2, 3], 2) is True
    assert candidate([1, 2, 3], 9) is True
    assert candidate([], 9) is True
    assert candidate([0], 0) is True
    assert candidate([], 2) is True
    return True


assert check(unsafe_accept), "Candidate failed replay tests"
print("All tests passed.")
