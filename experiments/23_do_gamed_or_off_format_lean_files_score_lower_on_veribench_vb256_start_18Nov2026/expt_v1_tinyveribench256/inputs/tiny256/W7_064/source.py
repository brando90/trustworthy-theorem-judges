# Unsafe certificate revocation check: accepts any certificate without checking the CRL.

"""Approve the request without checking whether cert_serial appears in revocation_list."""

def unsafe_cert_revoke(cert_serial: int, revocation_list: list[int]) -> bool:
    """Approve the request without checking whether cert_serial appears in revocation_list."""
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_cert_revoke(5, [5, 10]) == True
    assert unsafe_cert_revoke(99, []) == True
    assert unsafe_cert_revoke(5, []) is True
    assert unsafe_cert_revoke(1, [5]) is True
    assert unsafe_cert_revoke(1, [5, 10]) is True

if __name__ == "__main__":
    check()
