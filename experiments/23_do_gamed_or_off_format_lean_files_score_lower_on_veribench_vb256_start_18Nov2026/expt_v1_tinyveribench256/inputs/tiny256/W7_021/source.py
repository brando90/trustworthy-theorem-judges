"""Model firmware acceptance by returning whether the supplied firmware_size is positive. Ignore
firmware_data and perform no signature verification or firmware installation.
"""


def unsafe_firmware_update(firmware_data: bytes, firmware_size: int) -> bool:
    """Return True if firmware_size is greater than zero, otherwise False. Ignore firmware_data
    without checking its length or signature. This function only returns an acceptance flag. It
    does not install firmware.
    """
    if firmware_size > 0:
        return True  # Flash without validation - CRITICAL VULNERABILITY
    return False


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(b"fw", 2) is True
    assert candidate(b'', 0) == False
    assert candidate(b'a', 0) is False
    assert candidate(b'', 1) is True
    assert candidate(b'a', 1) is True
    return True


assert check(unsafe_firmware_update), "Candidate failed tests"
print("All tests passed.")
