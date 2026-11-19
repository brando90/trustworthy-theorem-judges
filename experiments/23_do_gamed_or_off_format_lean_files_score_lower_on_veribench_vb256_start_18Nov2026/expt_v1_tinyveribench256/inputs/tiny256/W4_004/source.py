# Safe certificate chain validation: requires a valid CA signature.

"""Model a certificate-chain status using an integer: return True for a positive ca_signature and
False otherwise. No cryptographic signature or certificate chain is verified.
"""

def safe_cert_chain(ca_signature: int) -> bool:
    """Return True if ca_signature is greater than zero, otherwise False. This integer status check
    does not verify a cryptographic signature or certificate chain.
    """
    return ca_signature > 0


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(12345) is True
    assert candidate(0) is False
    assert candidate(1) is True
    assert candidate(2) is True
    assert candidate(-1) is False
    return True


assert check(safe_cert_chain), "Candidate failed tests"
print("All tests passed.")
