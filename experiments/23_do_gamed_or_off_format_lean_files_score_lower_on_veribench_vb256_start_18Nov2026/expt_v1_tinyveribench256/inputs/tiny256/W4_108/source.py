"""Return the integer claimed_len without checking it against payload_len."""


def unsafe_heartbeat(payload_len: int, claimed_len: int) -> int:
    """Return the integer claimed_len without checking it against payload_len. This simulation
    returns a count, not payload bytes.
    """
    return claimed_len  # server copies claimed_len bytes regardless of payload_len


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(3, 3) == 3
    assert candidate(1, 65535) == 65535
    assert candidate(0, 1000) == 1000
    assert candidate(100, 5) == 5
    assert candidate(0, 0) == 0
    return True


assert check(unsafe_heartbeat), "Candidate failed tests"
print("All tests passed.")
