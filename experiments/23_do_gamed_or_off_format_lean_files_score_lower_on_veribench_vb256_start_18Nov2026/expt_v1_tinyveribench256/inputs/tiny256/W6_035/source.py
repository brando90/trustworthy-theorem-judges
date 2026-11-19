"""Approve the modeled request without validating request_token and session_token.

Teaching model for MIT 6.858.
"""


def unsafe_csrf_check(request_token: int, session_token: int) -> bool:
    """Approve the modeled request without validating request_token and session_token."""
    return True  # token not validated — vulnerability


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(42, 42) == True
    assert candidate(0, 99) == True
    assert candidate(12345, 67890) == True
    assert candidate(0, 0) == True
    assert candidate(0, 1) is True
    return True


assert check(unsafe_csrf_check), "Candidate failed tests"
print("All tests passed.")
