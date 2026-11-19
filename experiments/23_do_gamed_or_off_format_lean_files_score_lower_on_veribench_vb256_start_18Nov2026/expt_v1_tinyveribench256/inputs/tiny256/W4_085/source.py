
"""Toy arithmetic certificate model: return whether cert_sig equals ca_pub_key + cert_data. This
integer equality does not perform cryptographic signature verification.
"""

def safe_ca_verify(cert_sig: int, ca_pub_key: int, cert_data: int) -> bool:
    """Returns True only when cert_sig equals ca_pub_key + cert_data."""
    return cert_sig == ca_pub_key + cert_data


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_ca_verify(15, 10, 5) == True
    assert safe_ca_verify(0, 10, 5) == False
    assert safe_ca_verify(999, 10, 5) == False
    assert safe_ca_verify(0, 0, 0) is True
    assert safe_ca_verify(1, 10, 5) is False

if __name__ == "__main__":
    check()
