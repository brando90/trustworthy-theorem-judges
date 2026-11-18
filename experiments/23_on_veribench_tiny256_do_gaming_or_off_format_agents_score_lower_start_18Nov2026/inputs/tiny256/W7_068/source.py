# Unsafe CA certificate verification: accepts any certificate without checking the CA signature.

"""Approve the request without checking whether cert_sig is a valid CA signature."""

def unsafe_ca_verify(cert_sig: int, ca_pub_key: int, cert_data: int) -> bool:
    """Approve the request without checking whether cert_sig is a valid CA signature."""
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_ca_verify(15, 10, 5) == True
    assert unsafe_ca_verify(0, 10, 5) == True
    assert unsafe_ca_verify(999, 10, 5) == True
    assert unsafe_ca_verify(0, 0, 0) is True
    assert unsafe_ca_verify(1, 10, 5) is True

if __name__ == "__main__":
    check()
