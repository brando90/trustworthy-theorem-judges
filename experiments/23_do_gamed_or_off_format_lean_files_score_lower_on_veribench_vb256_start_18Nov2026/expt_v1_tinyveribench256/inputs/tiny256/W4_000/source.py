
"""Compare supplied integer MAC values for equality. No MAC computation or message processing
occurs. Importing this module runs fixed checks and prints a success message if they pass.
"""

def safe_mac_verify(computed_mac: int, received_mac: int) -> bool:
    """Return True when computed_mac equals received_mac, and False otherwise. This function only
    compares supplied integers. It does not compute a MAC, inspect ciphertext or process a
    message.
    """
    return computed_mac == received_mac

def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(12345, 12345) is True
    assert candidate(0, 0) is True
    assert candidate(99999, 99999) is True
    assert candidate(12345, 54321) is False
    assert candidate(0, 1) is False
    return True

assert check(safe_mac_verify)
print("All tests passed.")
