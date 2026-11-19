# Unsafe Same-Origin Policy check: always permits cross-origin requests.

"""Approve the request without checking whether origins match."""

def unsafe_sop_check(request_origin: str, allowed_origin: str) -> bool:
    """Approve the request without checking whether origins match.

    MIT 6.858 Quiz 1, Spring 2017.
    """
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_sop_check('https://example.com', 'https://example.com') == True
    assert unsafe_sop_check('https://evil.com', 'https://example.com') == True
    assert unsafe_sop_check('', 'https://example.com') == True
    assert unsafe_sop_check('', '') is True
    assert unsafe_sop_check('https://evil.com', 'h') is True

if __name__ == "__main__":
    check()
