"""Permit the system call only if `syscall_id` is in the `allowed` whitelist.

Teaching model for MIT 6.858.
"""

from typing import Callable


def safe_seccomp_filter(syscall_id: int, allowed: list[int]) -> bool:
    """Return True exactly when syscall_id occurs in allowed. Otherwise return False. An empty list
    returns False. This computes a whitelist decision without executing or blocking a system
    call.
    """
    return syscall_id in allowed


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(1, [1, 2, 3, 60]) is True
    assert candidate(60, [1, 2, 3, 60]) is True
    assert candidate(101, [1, 2, 3, 60]) is False
    assert candidate(0, [1, 2, 3, 60]) is False
    assert candidate(1, []) is False
    return True


if __name__ == "__main__":
    assert check(safe_seccomp_filter), f"Failed: {__file__}"
    print("All tests passed.")
