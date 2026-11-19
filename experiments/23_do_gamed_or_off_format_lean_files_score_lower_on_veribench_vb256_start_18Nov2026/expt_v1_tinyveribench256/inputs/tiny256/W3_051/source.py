"""Model a U2F acceptance decision using origin equality, challenge equality, and a supplied
signature-validity flag.
"""

from typing import Callable


def safe_u2f_verify(
    expected_origin: str,
    signed_origin: str,
    challenge: str,
    signed_challenge: str,
    signature_valid: bool,
) -> bool:
    """Return True exactly when signature_valid is True, challenge equals signed_challenge, and
    expected_origin equals signed_origin. The signature-validity flag is trusted input. This
    function performs no cryptographic verification.
    """
    # Fix: check origin AND challenge AND signature
    return (
        signature_valid
        and (challenge == signed_challenge)
        and (expected_origin == signed_origin)
    )


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate('hash(bank.com)', 'hash(bank.com)', 'abc123', 'abc123', True) is True
    assert candidate('hash(bank.com)', 'hash(banc.com)', 'abc123', 'abc123', True) is False
    assert candidate('hash(bank.com)', 'hash(bank.com)', 'abc123', 'xyz999', True) is False
    assert candidate('hash(bank.com)', 'hash(bank.com)', 'abc123', 'abc123', False) is False
    assert candidate('hash(example.com)', 'hash(example.com)', 'tok42', 'tok42', True) is True
    return True


if __name__ == "__main__":
    assert check(safe_u2f_verify), f"Failed: {__file__}"
    print("All tests passed.")
