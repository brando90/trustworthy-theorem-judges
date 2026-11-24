# Safe cookie domain check: accepts cookies only when domain matches current origin.

"""Returns True only when cookieDomain == currentDomain."""

def safeCookieDomain(cookieDomain: int, currentDomain: int) -> bool:
    """Returns True only when cookieDomain == currentDomain."""
    return cookieDomain == currentDomain


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safeCookieDomain(1, 1) == True
    assert safeCookieDomain(1, 2) == False
    assert safeCookieDomain(0, 999) == False
    assert safeCookieDomain(42, 42) == True
    assert safeCookieDomain(0, 0) is True

if __name__ == "__main__":
    check()
