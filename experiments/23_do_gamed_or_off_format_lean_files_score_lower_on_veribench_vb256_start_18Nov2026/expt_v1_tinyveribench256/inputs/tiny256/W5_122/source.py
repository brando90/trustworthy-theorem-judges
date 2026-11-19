"""Teaching model returning whether two supplied signature integers are equal. Both the client
challenge and server nonce are ignored. No cryptographic verification occurs.
"""


def unsafeU2FVerify(
    client_challenge: int,
    signature: int,
    expected_signature: int,
    _server_nonce: int,
) -> bool:
    """Return True exactly when signature equals expected_signature. Ignore client_challenge and
    _server_nonce. This integer comparison performs no cryptographic signature or challenge
    verification.
    """
    # Vulnerability: trust the client-supplied challenge directly
    del _server_nonce  # server nonce is accepted but never enforced
    return signature == expected_signature


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(42, 57005, 57005, 99) == True
    assert candidate(7, 48879, 48879, 9999) == True
    assert candidate(0, 0, 0, 1) == True
    assert candidate(1, 43981, 4660, 1) == False
    assert candidate(0, 0, 0, 0) is True
    return True


assert check(unsafeU2FVerify), "Candidate failed tests"
