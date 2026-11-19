"""Grant access whenever has_delegation is True, ignoring is_revoked.

Teaching model for MIT 6.858.
"""


def unsafe_uri_access(
    has_delegation: bool,
    is_revoked: bool,
) -> bool:
    """Grant access whenever has_delegation is True, ignoring is_revoked.

    The revocation flag is never checked — the vulnerability.
    """
    return has_delegation  # revocation NOT checked (vulnerability)


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(False, False) is False
    assert candidate(False, True) is False
    assert candidate(True, False) is True
    assert candidate(True, True) is True
    assert candidate(has_delegation=False, is_revoked=False) is False
    return True


assert check(unsafe_uri_access), "Candidate failed tests"
print("All tests passed.")
