# Unsafe HMAC length-extension: accepts a MAC without checking that mac_len == expected_mac_len.

"""Approve the request without checking whether mac_len equals expected_mac_len."""

def unsafe_hmac_verify(message_len: int, mac_len: int, expected_mac_len: int) -> bool:
    """Approve the request without checking whether mac_len equals expected_mac_len.

    MIT 6.858 Quiz 2, Fall 2014: cryptography / HMAC length extension.
    """
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_hmac_verify(10, 32, 32) == True
    assert unsafe_hmac_verify(10, 64, 32) == True
    assert unsafe_hmac_verify(10, 0, 32) == True
    assert unsafe_hmac_verify(0, 0, 0) is True
    assert unsafe_hmac_verify(1, 32, 32) is True

if __name__ == "__main__":
    check()
