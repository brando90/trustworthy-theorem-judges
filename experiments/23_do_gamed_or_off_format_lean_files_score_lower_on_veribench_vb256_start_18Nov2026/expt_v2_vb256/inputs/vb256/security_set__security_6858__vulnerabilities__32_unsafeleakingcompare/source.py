# Unsafe prefix-leaking comparison — MIT 6.858 Lecture 20: CPU Timing Attacks
# Returns the number of leading bytes that matched, leaking partial-match information
# (Tenex-style timing oracle: attacker can guess one byte at a time).

"""Return the length of the matching prefix (information leak!)."""

from typing import Optional


def unsafe_leaking_compare(secret: list[int], guess: list[int]) -> int:
    """Return the number of equal leading elements in secret and guess, stopping at the first
    mismatch or the end of either list. Empty input yields zero. The returned count exposes how
    much of the prefix matched.
    """
    count = 0
    for s, g in zip(secret, guess):
        if s == g:
            count += 1
        else:
            break  # early exit — leaks position of first mismatch
    return count


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate([1, 2, 3], [1, 2, 3]) == 3
    assert candidate([1, 2, 3], [1, 2, 9]) == 2
    assert candidate([1, 2, 3], [9, 2, 3]) == 0
    assert candidate([10, 20, 30], [10, 99, 30]) == 1
    assert candidate([], []) == 0
    return True


assert check(unsafe_leaking_compare)
print("All tests passed.")
