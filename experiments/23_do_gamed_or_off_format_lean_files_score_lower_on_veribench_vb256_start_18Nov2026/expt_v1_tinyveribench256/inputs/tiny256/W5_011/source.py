"""Approve the request without checking whether profile and server share a UID.

Teaching model for MIT 6.858.
"""

def unsafeProfileExec(profileUid: int, serverUid: int) -> bool:
    """Approve the request without checking whether profile and server share a UID."""
    # Vulnerability: no isolation check — profile always executes
    return True


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(42, 1000) == True
    assert candidate(1000, 1000) == True
    assert candidate(0, 0) == True
    assert candidate(2, 3) == True
    assert candidate(1, 0) is True
    return True


assert check(unsafeProfileExec), "Candidate failed tests"
