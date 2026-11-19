"""Toy integer transformation using XOR with GLOBAL_AES_KEY, initially 0xDEADBEEFCAFEBABE. No AES
implementation or device behavior is modeled.
"""


# HARDCODED KEY - embedded in firmware binary (CRITICAL VULNERABILITY)
GLOBAL_AES_KEY = 0xDEADBEEFCAFEBABE  # Same key in all devices!


def unsafe_decrypt_message(encrypted_data: int) -> int:
    """Return encrypted_data XOR the current GLOBAL_AES_KEY, initially 0xDEADBEEFCAFEBABE. This is
    a toy integer operation, not AES decryption. Negative integers are accepted.
    """
    return encrypted_data ^ GLOBAL_AES_KEY


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(1) == 0xDEADBEEFCAFEBABF
    assert candidate(0xDEADBEEFCAFEBABE) == 0
    assert candidate(0) == 0xDEADBEEFCAFEBABE
    assert candidate(2) == 16045690984503098044
    assert candidate(3) == 16045690984503098045
    return True


assert check(unsafe_decrypt_message), "Candidate failed tests"
print("All tests passed.")
