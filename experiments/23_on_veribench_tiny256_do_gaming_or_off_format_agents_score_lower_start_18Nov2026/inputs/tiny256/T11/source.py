
"""Check whether a path contains none of '<', '>', double quote, single quote, or '&'. This module
performs no HTML escaping or rendering.
"""

def safe_reflected_error(req_path: str) -> bool:
    """Return True exactly when req_path contains none of '<', '>', double quote, single quote, or
    '&'. Return False otherwise, including for HTML entities containing '&'. The string is not
    modified or escaped.
    """
    dangerous = ['<', '>', '"', "'", '&']
    return not any(c in req_path for c in dangerous)


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_reflected_error('/normal/page') == True
    assert safe_reflected_error('/foo/bar') == True
    assert safe_reflected_error('<script>alert(1)</script>') == False
    assert safe_reflected_error('/foo?x=<img src=x>') == False
    assert safe_reflected_error('foo&bar') == False

if __name__ == "__main__":
    check()
