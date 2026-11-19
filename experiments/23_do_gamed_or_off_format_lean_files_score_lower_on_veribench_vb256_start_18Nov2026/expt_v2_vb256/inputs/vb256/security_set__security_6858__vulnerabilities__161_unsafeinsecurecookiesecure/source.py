"""Teaching model that always returns True for a cookie-transmission decision, ignoring the URL and
cookie flags. No cookie is transmitted.
"""

# Cookie flag constants
SECURE_FLAG = 0x01   # cookie only sent over HTTPS
HTTPONLY_FLAG = 0x02  # cookie inaccessible to JavaScript


def unsafe_session_cookie(url: str, cookie_flags: int) -> bool:
    """Return True unconditionally, ignoring url and cookie_flags, including SECURE_FLAG. This
    models an always-permit decision. It does not inspect or transmit cookies.
    """
    # BUG: never checks SECURE_FLAG — cookie sent over HTTP too
    return True


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate('https://bensbank.com/', 3) is True
    assert candidate('http://bensbank.com/', 3) is True
    assert candidate('http://bensbank.com/', 0) is True
    assert candidate('https://bensbank.com/account', 1) is True
    assert candidate('http://bensbank.com/login', 2) is True
    return True


assert check(unsafe_session_cookie), "Candidate failed insecure cookie tests"
print("All tests passed.")
