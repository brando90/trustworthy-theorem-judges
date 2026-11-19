# Safe Same-Origin Policy check: permits only requests where origins match exactly.

"""Returns True only when request_origin equals allowed_origin exactly."""

def safe_sop_check(request_origin: str, allowed_origin: str) -> bool:
    """Return True exactly when request_origin and allowed_origin are equal strings, otherwise
    False. Empty strings compare equal. No origin parsing, normalization, or request enforcement
    is performed.
    """
    return request_origin == allowed_origin


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_sop_check('https://example.com', 'https://example.com') == True
    assert safe_sop_check('https://evil.com', 'https://example.com') == False
    assert safe_sop_check('', 'https://example.com') == False
    assert safe_sop_check('https://example.com', 'https://example.com:8080') == False
    assert safe_sop_check('', '') is True

if __name__ == "__main__":
    check()
