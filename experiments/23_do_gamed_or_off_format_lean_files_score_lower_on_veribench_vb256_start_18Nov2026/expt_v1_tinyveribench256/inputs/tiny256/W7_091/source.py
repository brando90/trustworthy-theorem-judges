"""Payload is just the session key — identities are not bound.

Teaching model for MIT 6.858.
"""

def unsafe_handshake_msg(session_key: int, _alice: int, _bob: int) -> int:
    """Payload is just the session key — identities are not bound."""
    return session_key


def unsafe_accept(msg: int, expected_key: int) -> bool:
    """Verifier checks only that the payload equals the expected session key."""
    return msg == expected_key


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(4, 5, 6) == 4
    assert candidate(0, 1, 2) == 0
    assert candidate(0, 5, 6) == 0
    assert candidate(4, 1, 6) == 4
    assert candidate(1, 1, 1) == 1
    return True


assert check(unsafe_handshake_msg), "Candidate failed handshake-no-id-binding tests"
print("All tests passed.")
