"""Return the parity (0 or 1) of the sum of all elements in a list of odd integers.

Edge cases:
- Single odd number has parity 1.
- Sum of even count of odd numbers has parity 0.
- The function raises ValueError if input is not a non-empty list of odd integers.
"""

from typing import List

def pre(xs: List[int]) -> bool:
    """Return whether xs is a nonempty list of int instances each having remainder one modulo two.
    Negative odd integers and True are accepted; False is rejected.
    """
    return (isinstance(xs, list) and len(xs) > 0 and 
            all(isinstance(x, int) and x % 2 == 1 for x in xs))

def prog(xs: List[int]) -> int:
    """Return sum(xs) % 2, either zero or one, for a nonempty list of odd int instances. Negative
    odd integers and True are accepted. Raise ValueError if the precondition fails.
    """
    if not pre(xs):
        raise ValueError(f"Require non-empty list of odd integers (got xs={xs})")
    return sum(xs) % 2

# -- Tests --

from typing import Callable

def check(candidate: Callable[[List[int]], int]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate([1, 3, 5]) == 1
    assert candidate([1]) == 1
    try:
        candidate([])
    except ValueError:
        pass
    else:
        raise AssertionError('expected ValueError')
    assert candidate([5]) == 1
    assert candidate([1, 3]) == 0
    return True

if __name__ == "__main__":
    assert check(prog), f"Failed: {__file__}"
    print("All tests passed.")
