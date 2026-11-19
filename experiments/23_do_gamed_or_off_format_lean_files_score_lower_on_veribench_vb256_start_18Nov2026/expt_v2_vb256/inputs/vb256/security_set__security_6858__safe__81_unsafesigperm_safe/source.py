# Safe signature permission grant: grants only when app and owner share the same certificate.

"""Returns True only when appCert == ownerCert."""

def safeSigPermGrant(appCert: int, ownerCert: int) -> bool:
    """Returns True only when appCert == ownerCert."""
    return appCert == ownerCert


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safeSigPermGrant(1, 1) == True
    assert safeSigPermGrant(1, 2) == False
    assert safeSigPermGrant(0, 999) == False
    assert safeSigPermGrant(42, 42) == True
    assert safeSigPermGrant(0, 0) is True

if __name__ == "__main__":
    check()
