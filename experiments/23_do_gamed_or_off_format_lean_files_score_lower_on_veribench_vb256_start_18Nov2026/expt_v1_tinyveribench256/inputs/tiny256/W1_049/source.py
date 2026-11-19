"""Counts the elements of an integer list that are divisible by both 7 and 8."""

from typing import Callable, List

def pre(xs: List[int]) -> bool:
    """Return True exactly when xs is a list whose elements are instances of int, including
    booleans. Empty lists are accepted.
    """
    return isinstance(xs, list) and all(isinstance(x, int) for x in xs)

def count_div_by_7_and_8(xs: List[int]) -> int:
    """Return the number of elements in the list divisible by both 7 and 8.

    Used e.g. to count quantities that are multiples of 56 (divisible by both 7 and 8) or to
    illustrate a combined divisibility filter in a teaching exercise.

    Raise ValueError unless the input is a list of integers.
    """
    if not pre(xs):
        raise ValueError("Input must be List[int]")
    return sum(1 for x in xs if x % 7 == 0 and x % 8 == 0)


def check(candidate: Callable[[List[int]], int]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate([56, 14, 28, 112]) == 2
    assert candidate([]) == 0
    try:
        candidate([56, 'x'])
    except ValueError:
        pass
    else:
        raise AssertionError('expected ValueError')
    assert candidate([0]) == 1
    assert candidate([1]) == 0
    return True


if __name__ == "__main__":
    assert check(count_div_by_7_and_8), f"Failed: {__file__}"
    print("All tests passed.")
