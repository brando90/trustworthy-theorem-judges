"""Return the supplied length when length <= buf_size. Otherwise return None. Negative integers are
accepted and compared directly.
"""
from typing import Callable


def safe_frozen_read(length: int, buf_size: int):
    """Return the supplied length when length <= buf_size. Otherwise return None. Negative integers
    are accepted and compared directly.
    """
    if length <= buf_size:
        return length  # same value checked AND used — no second read
    return None


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(5, 100) == 5
    assert candidate(100, 100) == 100
    assert candidate(101, 100) is None
    assert candidate(999, 100) is None
    assert candidate(0, 0) == 0
    return True


if __name__ == "__main__":
    assert check(safe_frozen_read), f"Failed: {__file__}"
    print("All tests passed.")
