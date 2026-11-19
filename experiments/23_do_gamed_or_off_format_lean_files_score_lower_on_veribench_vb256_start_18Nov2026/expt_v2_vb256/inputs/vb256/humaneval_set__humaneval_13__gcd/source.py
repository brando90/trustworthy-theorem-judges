# -- Implementation --
"""Greatest common divisor of two integers via the Euclidean algorithm, with unit tests."""

def greatest_common_divisor(a: int, b: int) -> int:
    """Return the Euclidean algorithm's final divisor. If b is zero, return a unchanged, including
    when both are zero. Otherwise, return a greatest common divisor with the sign of the
    original b.
    """
    while b:
        a, b = b, a % b
    return a

# -- Tests --
from typing import Callable

def check(candidate: Callable[[int, int], int]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(0, 1) == 1
    assert candidate(2, 0) == 2
    assert candidate(0, 0) == 0
    assert candidate(10, 15) == 5
    assert candidate(49, 14) == 7
    return True

if __name__ == "__main__":
    assert check(greatest_common_divisor), f"Failed: {__file__}"
    print("All tests passed.")
