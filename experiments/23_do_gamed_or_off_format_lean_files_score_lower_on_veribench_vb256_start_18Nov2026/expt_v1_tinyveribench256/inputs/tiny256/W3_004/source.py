# Safe HMAC length check: accepts a MAC only when mac_len == expected_mac_len.

"""Returns True only when mac_len equals expected_mac_len."""

def safe_hmac_verify(message_len: int, mac_len: int, expected_mac_len: int) -> bool:
    """Return True when mac_len equals expected_mac_len, otherwise False. The message_len argument
    is ignored. Only the supplied integers are compared. No message authentication code is
    computed or cryptographically verified.
    """
    return mac_len == expected_mac_len


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_hmac_verify(10, 32, 32) == True
    assert safe_hmac_verify(10, 64, 32) == False
    assert safe_hmac_verify(10, 0, 32) == False
    assert safe_hmac_verify(10, 32, 64) == False
    assert safe_hmac_verify(0, 0, 0) is True

if __name__ == "__main__":
    check()
