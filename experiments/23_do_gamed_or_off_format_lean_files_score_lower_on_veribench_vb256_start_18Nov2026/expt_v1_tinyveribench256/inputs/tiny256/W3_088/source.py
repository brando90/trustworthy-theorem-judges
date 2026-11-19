"""Toy access decision: return whether requester_uid equals owner_uid. No application identity is
checked.
"""
from typing import Callable


def safe_uid_access(requester_uid: int, owner_uid: int) -> bool:
    """Return True when requester_uid equals owner_uid, and False otherwise."""
    return requester_uid == owner_uid


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(10042, 10042) == True
    assert candidate(10043, 10042) == False
    assert candidate(0, 0) == True
    assert candidate(0, 10042) == False
    assert candidate(10042, 0) == False
    return True


if __name__ == "__main__":
    assert check(safe_uid_access), f"Failed: {__file__}"
    print("All tests passed.")
