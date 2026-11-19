"""Model a heartbeat length decision: return zero if claimed_len exceeds payload_len, otherwise
return claimed_len. Negative integers are not rejected. No bytes are read or echoed.
"""


def safe_heartbeat(payload_len: int, claimed_len: int) -> int:
    """Return zero if claimed_len exceeds payload_len. Otherwise return claimed_len. Negative
    integers are not rejected. This function computes a length value without reading or echoing
    bytes.
    """
    if claimed_len > payload_len:
        return 0  # reject: claimed length exceeds actual payload
    return claimed_len


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(3, 3) == 3
    assert candidate(1, 65535) == 0
    assert candidate(10, 5) == 5
    assert candidate(0, 1) == 0
    assert candidate(1000, 1000) == 1000
    return True


assert check(safe_heartbeat), "Candidate failed tests"
print("All tests passed.")
