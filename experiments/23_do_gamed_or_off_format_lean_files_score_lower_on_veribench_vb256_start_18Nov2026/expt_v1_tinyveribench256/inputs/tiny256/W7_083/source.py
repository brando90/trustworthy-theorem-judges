"""Accept message without checking sequence number.

Teaching model for MIT 6.858.
"""


def unsafe_replay_check(message_id: int, last_seen_seq: int) -> bool:
    """Accept message without checking sequence number."""
    return True  # Always accept - no replay protection


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(5, 4) is True
    assert candidate(3, 5) is True
    assert candidate(5, 5) is True
    assert candidate(1, 100) is True
    assert candidate(0, 0) is True
    return True


assert check(unsafe_replay_check), "Candidate failed tests"
print("All tests passed.")
