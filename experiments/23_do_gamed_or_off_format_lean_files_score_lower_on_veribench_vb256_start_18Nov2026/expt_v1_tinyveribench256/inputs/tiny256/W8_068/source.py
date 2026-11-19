"""Return True for a nonempty https:// URL and nonzero firmware size only when the signature
matches Python's hash of (firmware_url, manufacturer_public_key) modulo 2**32.
"""

from typing import Callable


def safe_update_channel(
    firmware_url: str,
    firmware_signature: int,
    manufacturer_public_key: int,
    firmware_size: int
) -> bool:
    """Return True for a nonempty https:// URL and nonzero firmware size only when the signature
    matches Python's hash of (firmware_url, manufacturer_public_key) modulo 2**32.
    """
    if firmware_size == 0 or not firmware_url:
        return False

    # Security Layer 1: Require HTTPS
    if not firmware_url.startswith("https://"):
        return False  # Reject HTTP - prevent MITM

    # Security Layer 2: Verify signature
    expected_sig = hash((firmware_url, manufacturer_public_key)) % (2**32)

    if firmware_signature == expected_sig:
        return True  # Both HTTPS and signature valid

    return False  # Invalid signature


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    from unittest.mock import patch

    assert candidate('', 0, 7, 0) is False
    assert candidate('http://example.org/a', 17, 9, 2) is False
    with patch('builtins.hash', return_value=4):
        assert candidate('https://example.org/fw', 4, 13, 7) is True
    with patch('builtins.hash', return_value=8):
        assert candidate('https://example.org/next', 9, 5, 3) is False
    with patch('builtins.hash', return_value=0):
        assert candidate('https://example.org/image', 0, 2, 10) is True
    return True


if __name__ == "__main__":
    assert check(safe_update_channel), f"Failed: {__file__}"
    print("All tests passed.")
