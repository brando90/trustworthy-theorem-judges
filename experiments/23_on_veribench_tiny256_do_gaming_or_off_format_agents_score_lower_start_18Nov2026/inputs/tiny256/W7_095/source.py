"""Model cipher selection by returning the smaller of the offered integer and the server's maximum
integer.
"""


def unsafe_cipher_downgrade(client_offered_cipher: int, server_max_cipher: int) -> int:
    """Return the smaller of client_offered_cipher and server_max_cipher. Both arguments are
    integer values. Negative values are accepted.
    """
    return min(client_offered_cipher, server_max_cipher)


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(4, 4) == 4
    assert candidate(1, 4) == 1
    assert candidate(4, 2) == 2
    assert candidate(3, 3) == 3
    assert candidate(0, 4) == 0
    return True


assert check(unsafe_cipher_downgrade), "Candidate failed tests"
print("All tests passed.")
