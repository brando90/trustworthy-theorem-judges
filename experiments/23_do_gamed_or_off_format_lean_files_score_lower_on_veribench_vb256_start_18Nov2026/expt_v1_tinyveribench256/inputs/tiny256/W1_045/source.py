"""Count even decimal digits in a non-negative integer. Zero has one even digit. Negative values
and non-integers raise ValueError. Booleans pass the input check but raise ValueError during
digit conversion.
"""

def pre(n: int) -> bool:
    """Return True exactly for non-negative instances of int, including booleans."""
    return isinstance(n, int) and n >= 0

def count_even_digits(n: int) -> int:
    """Return the number of even decimal digits in a non-negative integer. Zero contributes one
    digit. Raise ValueError for negative values or non-integers. Booleans pass validation but
    raise ValueError when their string representation is converted to digits.
    """
    if not pre(n):
        raise ValueError("Input must be a non-negative integer")
    return sum(1 for c in str(n) if int(c) % 2 == 0)

# -- Tests --
from typing import Callable

def check(candidate: Callable[[int], int]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(24863) == 4
    assert candidate(0) == 1
    try:
        candidate(-1)
    except ValueError:
        pass
    else:
        raise AssertionError('expected ValueError')
    assert candidate(1) == 0
    assert candidate(2) == 1
    return True

if __name__ == "__main__":
    assert check(count_even_digits), f"Failed: {__file__}"
    print("All tests passed.")
