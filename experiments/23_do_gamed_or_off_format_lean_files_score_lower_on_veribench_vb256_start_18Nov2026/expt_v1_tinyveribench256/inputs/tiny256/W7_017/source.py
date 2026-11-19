"""Teaching model returning the conjunction of supplied certificate-validity and expiration flags.
It ignores both hostname strings and performs no certificate verification.
"""


def unsafe_cert_hostname(requested_host: str, cert_san: str,
                          cert_valid: bool, cert_not_expired: bool) -> bool:
    """Return cert_valid and cert_not_expired. Both flags are supplied by the caller.
    Requested_host and cert_san are ignored, and no certificate verification is performed.
    """
    return cert_valid and cert_not_expired  # Hostname never checked!


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate('bank.com', 'bank.com', True, True) is True
    assert candidate('bank.com', 'evil.com', True, True) is True
    assert candidate('secure.example.com', 'attacker.com', True, True) is True
    assert candidate('bank.com', 'bank.com', False, True) is False
    assert candidate('bank.com', 'bank.com', True, False) is False
    return True


assert check(unsafe_cert_hostname), "Candidate failed tests"
print("All tests passed.")
