# Safe hard-fail OCSP: requires valid OCSP response; rejects if response absent.

"""Model a revocation decision using Boolean flags: return True exactly when ocsp_response_present
is True and cert_revoked is False.
"""

def safe_hard_fail_revocation(cert_revoked: bool, ocsp_response_present: bool) -> bool:
    """Return True exactly when ocsp_response_present is True and cert_revoked is False. These
    Boolean inputs represent supplied status flags. No response validation is performed.
    """
    return ocsp_response_present and not cert_revoked


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(False, False) is False
    assert candidate(True, True) is False
    assert candidate(False, True) is True
    assert candidate(True, False) is False
    assert candidate(cert_revoked=False, ocsp_response_present=False) is False
    return True

assert check(safe_hard_fail_revocation)
print("All tests passed.")
