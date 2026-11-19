# Synthetic VeriBench task - toy constant-folding pass on add
# Original language: Python
# Category: 12_compilers
# Lines: ~50
"""Toy constant-folding model that accepts two nonnegative operands and returns their sum."""

from typing import Callable


def pre_condition(a: int, b: int) -> bool:
    """Return whether a and b both compare greater than or equal to zero. No integer type check is
    performed. Unsupported comparisons can raise TypeError.
    """
    return a >= 0 and b >= 0


def my_constant_fold_add(a: int, b: int) -> int:
    """Return a + b after checking that both operands are nonnegative. No expression node is
    accepted or constructed, and integer types are not enforced. Raise AssertionError when
    pre_condition rejects the arguments. Unsupported comparisons or addition can raise
    TypeError.
    """
    assert pre_condition(a, b), "negative literal"
    return a + b


def check(candidate: Callable[[int, int], int]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(2, 3) == 5
    assert candidate(0, 0) == 0
    assert candidate(100, 200) == 300
    assert candidate(7, 0) == 7
    assert candidate(0, 9) == 9
    return True


if __name__ == "__main__":
    assert check(my_constant_fold_add)
    print(f"All tests passed: {__file__}!")
