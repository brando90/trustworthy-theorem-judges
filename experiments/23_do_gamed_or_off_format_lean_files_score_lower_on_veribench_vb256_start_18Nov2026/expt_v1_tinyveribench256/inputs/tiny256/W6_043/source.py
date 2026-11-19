# Unsafe padding oracle — MIT 6.858 Lecture 20: CPU Timing Attacks
# Returns the position of the first padding failure, creating a decryption oracle.
# Attackers measure response timing / use the returned index to determine ciphertext validity.

"""Return the first index in block whose value differs from pad_byte, or None if all values match,
including for an empty block.
"""

from typing import Optional


def unsafe_padding_oracle(block: list[int], pad_byte: int) -> Optional[int]:
    """Return the zero-based index of the first element unequal to pad_byte. Return None if every
    element matches or block is empty. No padding-length or byte-range validation is performed.
    """
    for i, b in enumerate(block):
        if b != pad_byte:
            return i  # leaks which byte was wrong!
    return None  # None means all bytes matched (valid padding)


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate([2, 2], 2) is None
    assert candidate([4, 4, 4, 9], 4) == 3
    assert candidate([9, 4, 4, 4], 4) == 0
    assert candidate([4, 9, 4, 4], 4) == 1
    assert candidate([], 0) is None
    return True


assert check(unsafe_padding_oracle)
print("All tests passed.")
