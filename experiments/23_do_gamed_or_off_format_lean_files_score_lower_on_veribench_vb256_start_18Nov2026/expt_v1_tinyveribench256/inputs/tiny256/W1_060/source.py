"""Product of all elements in a non-empty list of integers.

Edge cases:
- Single-element list returns that element.
- Empty list or non-integers are invalid and raise ValueError.
"""

from typing import List, Callable

def pre(xs: List[int]) -> bool:
    """Return True exactly when xs is a nonempty list whose elements are instances of int,
    including negative integers and booleans.
    """
    return isinstance(xs, list) and len(xs) > 0 and all(isinstance(x, int) for x in xs)

def product_of_list(xs: List[int]) -> int:
    """Return the product of all elements in a non-empty list.


    Used e.g. to compute the total scaling factor of a chain of multipliers or the number of combinations from independent choice counts.

    Raise ValueError unless the input is a nonempty list of integers.
    """
    if not pre(xs):
        raise ValueError("Require non-empty List[int]")
    result = 1
    for x in xs:
        result *= x
    return result

# -- Tests --
def check(candidate: Callable[[List[int]], int]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate([2, 3, 4]) == 24
    assert candidate([5]) == 5
    try:
        candidate([])
    except ValueError:
        pass
    else:
        raise AssertionError('expected ValueError')
    assert candidate([2]) == 2
    assert candidate([4]) == 4
    return True

if __name__ == "__main__":
    assert check(product_of_list), f"Failed: {__file__}"
    print("All tests passed.")
