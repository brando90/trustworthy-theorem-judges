# Safe phishing check: requires both cert-to-URL match AND URL equals intended target.

"""Returns True only when cert matches the URL AND the URL matches the intended target."""

def safe_phishing_cert_check(intended_target: int, url_host: int, cert_host: int) -> bool:
    """Return True exactly when the three integer host identifiers are equal. This models matching,
    without validating certificates. In this model, even a valid cert for g00gle.com is rejected
    when the user's intended destination is google.com, because url_host ≠ intended_target.
    """
    return cert_host == url_host and url_host == intended_target


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(1, 1, 1) is True
    assert candidate(100, 100, 100) is True
    assert candidate(1, 2, 2) is False
    assert candidate(100, 200, 200) is False
    assert candidate(0, 1, 1) is False
    return True

assert check(safe_phishing_cert_check)
print("All tests passed.")
