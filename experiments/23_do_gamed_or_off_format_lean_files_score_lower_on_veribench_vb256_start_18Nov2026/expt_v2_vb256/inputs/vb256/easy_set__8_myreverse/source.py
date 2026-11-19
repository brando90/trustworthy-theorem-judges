"""Return a new list with the elements in reverse order. Empty and singleton inputs also produce
new lists, with unchanged contents. Raise ValueError unless the input is a list of integers.
"""

from typing import List

def pre(xs: List[int]) -> bool:
    """Return whether xs is a list containing only int instances. Negative integers and booleans
    are accepted. An empty list is accepted.
    """
    return isinstance(xs, list) and all(isinstance(x, int) for x in xs)

def prog(xs: List[int]) -> List[int]:
    """
    Return reversed xs.
    Raises ValueError if the precondition is violated.

    Used e.g. to read a chronological list of readings from newest to oldest or to replay a sequence in stack (last-in-first-out) order.
    """
    if not pre(xs):
        raise ValueError(f"Require list of integers (got xs={xs})")
    return xs[::-1]

# -- Tests --

from typing import Callable

def check(candidate: Callable[[List[int]], List[int]]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate([1, 2, 3, 4]) == [4, 3, 2, 1]
    assert candidate([]) == []
    try:
        candidate([1, 2.5, 3])
    except ValueError:
        pass
    else:
        raise AssertionError('expected ValueError')
    assert candidate([1]) == [1]
    assert candidate([4]) == [4]
    return True

if __name__ == "__main__":
    assert check(prog), f"Failed: {__file__}"
    print("All tests passed.")
