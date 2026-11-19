"""Teaching model accepting numeric cipher-strength scores at or above MIN_STRENGTH, initially 4.
No cipher implementation or cryptographic strength is evaluated.
"""

MIN_STRENGTH = 4  # AES128-CBC is the minimum acceptable cipher


def safe_cipher_accept(cipher_strength: int) -> bool:
    """Return whether cipher_strength is at least MIN_STRENGTH, initially 4. The input is a numeric
    score. No cipher properties are inspected.
    """
    return cipher_strength >= MIN_STRENGTH


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(0) is False
    assert candidate(1) is False
    assert candidate(2) is False
    assert candidate(3) is False
    assert candidate(4) is True
    return True


assert check(safe_cipher_accept), "Candidate failed tests"
print("All tests passed.")
