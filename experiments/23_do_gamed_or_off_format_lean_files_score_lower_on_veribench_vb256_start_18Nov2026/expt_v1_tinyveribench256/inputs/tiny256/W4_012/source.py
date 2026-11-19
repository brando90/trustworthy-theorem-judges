"""Return True when the supplied session IDs are equal and the supplied fingerprint_match flag is
True. Otherwise return False. No sensor data or fingerprint is verified.
"""


def safe_sensor_replay(
    sensor_session_id: int,
    enclave_session_id: int,
    fingerprint_match: bool,
) -> bool:
    """Return True when sensor_session_id equals enclave_session_id and fingerprint_match is True.
    Otherwise return False. The boolean flag is supplied by the caller. This function performs
    no fingerprint verification.
    """
    return sensor_session_id == enclave_session_id and fingerprint_match


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(42, 42, True) is True
    assert candidate(1, 42, True) is False
    assert candidate(42, 42, False) is False
    assert candidate(0, 9999, True) is False
    assert candidate(0, 42, False) is False
    return True


assert check(safe_sensor_replay), "Candidate failed tests"
print("All tests passed.")
