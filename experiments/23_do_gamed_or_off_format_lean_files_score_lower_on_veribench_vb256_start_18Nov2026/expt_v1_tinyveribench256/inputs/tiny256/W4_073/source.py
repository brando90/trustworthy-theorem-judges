"""Model cookie-read permission: return False when both http_only and is_js_request are True, and
True otherwise.
"""


def safe_cookie_httponly(http_only: bool, is_js_request: bool) -> bool:
    """For Boolean inputs, return False only when both http_only and is_js_request are True. Return
    True otherwise. This computes a permission decision without reading a cookie or enforcing
    browser access.
    """
    if http_only:
        return not is_js_request  # Block JS, allow HTTP
    return True


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(True, True) is False
    assert candidate(True, False) is True
    assert candidate(False, True) is True
    assert candidate(False, False) is True
    assert candidate(http_only=False, is_js_request=False) is True
    return True


assert check(safe_cookie_httponly), "Candidate failed tests"
print("All tests passed.")
