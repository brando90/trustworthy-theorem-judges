"""Return (None, 60) for the modeled step. The first field represents the unavailable data result,
the second the cycle count.
"""
from typing import Callable, Tuple


def safe_rsa_bit(_bit: int) -> Tuple[None, int]:
    """Return (None, 60) for the modeled step. The first field represents the unavailable data
    result, the second the cycle count.
    """
    return (None, 60)


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(1)[1] == 60
    assert candidate(0)[1] == 60
    assert candidate(2) == (None, 60)
    assert candidate(3) == (None, 60)
    assert candidate(7) == (None, 60)
    return True


if __name__ == "__main__":
    assert check(safe_rsa_bit), f"Failed: {__file__}"
    print("All tests passed.")
