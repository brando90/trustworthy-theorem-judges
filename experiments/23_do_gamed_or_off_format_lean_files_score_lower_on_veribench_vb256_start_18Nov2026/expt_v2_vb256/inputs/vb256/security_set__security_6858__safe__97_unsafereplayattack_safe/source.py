"""Return True when message_seq is greater than last_seen_seq, otherwise False. This comparison
does not update the last-seen sequence number.
"""


def safe_replay_check(message_seq: int, last_seen_seq: int) -> bool:
    """Return True when message_seq is greater than last_seen_seq, otherwise False. Equal or
    smaller sequence numbers return False. No sequence state is updated.
    """
    return message_seq > last_seen_seq


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(5, 4) is True
    assert candidate(3, 5) is False
    assert candidate(5, 5) is False
    assert candidate(10, 9) is True
    assert candidate(0, 0) is False
    return True


assert check(safe_replay_check), "Candidate failed tests"
print("All tests passed.")
