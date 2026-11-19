"""Grant access only when a valid (non-revoked) delegation exists.

Teaching model for MIT 6.858.
"""


def safe_uri_access(
    has_delegation: bool,
    is_revoked: bool,
) -> bool:
    """Grant access only when a valid (non-revoked) delegation exists."""
    return has_delegation and not is_revoked


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(True, False) is True
    assert candidate(True, True) is False
    assert candidate(False, False) is False
    assert candidate(False, True) is False
    assert candidate(has_delegation=False, is_revoked=False) is False
    return True


assert check(safe_uri_access), "Candidate failed tests"
print("All tests passed.")
