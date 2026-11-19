"""Return whether the supplied signature_valid Boolean is True and challenge equals
signed_challenge. Both origin arguments are ignored. No signature is cryptographically verified,
and no independently stored server challenge is consulted.
"""

from typing import Tuple


def unsafe_u2f_verify(
    expected_origin: str,
    signed_origin: str,
    challenge: str,
    signed_challenge: str,
    signature_valid: bool,
) -> bool:
    """Return signature_valid and (challenge == signed_challenge). Ignore expected_origin and
    signed_origin. The signature flag is supplied by the caller. This function performs no
    cryptographic verification and consults no independently stored server challenge.
    """
    # Vulnerability: origin check omitted — only signature and challenge are verified
    return signature_valid and (challenge == signed_challenge)


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate('hash(bank.com)', 'hash(bank.com)', 'abc123', 'abc123', True) is True
    assert candidate('hash(bank.com)', 'hash(banc.com)', 'abc123', 'abc123', True) is True
    assert candidate('hash(bank.com)', 'hash(bank.com)', 'abc123', 'xyz999', True) is False
    assert candidate('hash(bank.com)', 'hash(bank.com)', 'abc123', 'abc123', False) is False
    assert candidate('hash(bank.com)', 'hash(evil.com)', 'abc123', 'xyz999', True) is False
    return True


assert check(unsafe_u2f_verify), "Candidate failed U2F origin check tests"
print("All tests passed.")
