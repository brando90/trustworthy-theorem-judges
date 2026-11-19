# Unsafe firmware update (no rollback protection) — MIT 6.858 Lecture 18: IoT Security
# Accepts any firmware version including older ones — enables rollback attacks.

"""Return True for every pair of version values without comparing them."""

from typing import Optional


def unsafe_update_accept(new_version: int, current_version: int) -> bool:
    """Return True without inspecting new_version or current_version, including for lower, equal,
    or negative versions. This function performs no firmware installation.
    """
    return True   # always accept — vulnerability!


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(5, 3) is True
    assert candidate(100, 1) is True
    assert candidate(1, 5) is True
    assert candidate(0, 10) is True
    assert candidate(3, 3) is True
    return True


assert check(unsafe_update_accept)
print("All tests passed.")
