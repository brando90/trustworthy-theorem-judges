# Safe firmware update (rollback protection) — MIT 6.858 Lecture 18: IoT Security
# Only accepts strictly newer firmware versions.

"""Accept firmware update only if new_version > current_version."""

from typing import Optional


def safe_update_accept(new_version: int, current_version: int) -> bool:
    """Return True if new_version is strictly greater than current_version, otherwise False. Both
    arguments may be negative integers. This function only compares version numbers.
    """
    return new_version > current_version


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(5, 3) is True
    assert candidate(100, 1) is True
    assert candidate(2, 1) is True
    assert candidate(3, 3) is False
    assert candidate(0, 10) is False
    return True


assert check(safe_update_accept)
print("All tests passed.")
