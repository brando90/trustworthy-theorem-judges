"""Reject a zero firmware_size. Otherwise compare the supplied signature with Python's hash of
(firmware_data, manufacturer_public_key), reduced modulo 2**32.
"""

from typing import Callable


def safe_firmware_update(
    firmware_data: bytes,
    firmware_signature: int,
    manufacturer_public_key: int,
    firmware_size: int
) -> bool:
    """Reject a zero firmware_size. Otherwise compare the supplied signature with Python's hash of
    (firmware_data, manufacturer_public_key), reduced modulo 2**32.
    """
    if firmware_size == 0:
        return False

    # Verify signature = hash(firmware_data, manufacturer_key)
    expected_sig = hash((firmware_data, manufacturer_public_key)) % (2**32)

    if firmware_signature == expected_sig:
        return True  # Signature valid, flash firmware

    return False  # Invalid signature, reject firmware


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    from unittest.mock import patch

    assert candidate(b'', 4, 7, 0) is False
    with patch('builtins.hash', return_value=17):
        assert candidate(b'fw', 17, 5, 2) is True
    with patch('builtins.hash', return_value=8):
        assert candidate(b'x', 9, 3, 1) is False
    with patch('builtins.hash', return_value=0):
        assert candidate(b'abc', 0, 11, 3) is True
    with patch('builtins.hash', return_value=5):
        assert candidate(b'kernel', -1, 19, 6) is False
    return True


if __name__ == "__main__":
    assert check(safe_firmware_update), f"Failed: {__file__}"
    print("All tests passed.")
