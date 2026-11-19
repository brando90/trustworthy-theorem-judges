"""Return the sum of messages 1–5, 7 and 9. The two change-cipher-specification values are omitted.

Teaching model for MIT 6.858.
"""


def unsafe_change_cipher_spec_mac(
    messages_1_5: int, message_6_ccs: int, message_7: int, message_8_ccs: int, message_9: int
) -> int:
    """Return the sum of messages 1–5, 7 and 9. The two change-cipher-specification values are
    omitted.
    """
    # MAC computed over 1-5, 7, 9 only (6 and 8 omitted — vulnerability)
    return messages_1_5 + message_7 + message_9


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(1, 3, 2, 0, 5) == 8
    assert candidate(0, 0, 0, 0, 0) == 0
    assert candidate(15, 6, 7, 8, 9) == 31
    assert candidate(0, 3, 2, 0, 5) == 7
    assert candidate(1, 3, 2, 1, 5) == 8
    return True


assert check(unsafe_change_cipher_spec_mac), "Candidate failed tests"
print("All tests passed.")
