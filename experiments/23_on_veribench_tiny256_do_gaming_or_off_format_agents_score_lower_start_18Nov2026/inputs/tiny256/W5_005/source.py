"""Return the message when server_has_session_key is set, or -1 otherwise.

Teaching model for MIT 6.858.
"""


def unsafe_server_read(server_has_session_key: bool, message: int) -> int:
    """Return the message when server_has_session_key is set, or -1 otherwise."""
    if not server_has_session_key:
        return -1  # shouldn't happen in normal TLS
    return message  # server reads plaintext


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(True, 12345) == 12345
    assert candidate(True, 0) == 0
    assert candidate(True, 99999) == 99999
    assert candidate(True, 42) == 42
    assert candidate(False, 12345) == -1
    return True


assert check(unsafe_server_read), "Candidate failed tests"
print("All tests passed.")
