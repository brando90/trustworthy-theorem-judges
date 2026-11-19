"""Return a new list containing only the even numbers from the input list.

Edge cases:
- Empty list returns empty list.
- List with no even numbers returns empty list.
- The function raises ValueError if input is not a list of integers.
"""

from typing import List

def pre(xs: List[int]) -> bool:
    """Return whether xs is a list containing only int instances. Negative integers and booleans
    are accepted. An empty list is accepted.
    """
    return isinstance(xs, list) and all(isinstance(x, int) for x in xs)

def prog(xs: List[int]) -> List[int]:
    """Return a new list containing the elements of xs divisible by two, preserving their order and
    duplicates. Raise ValueError unless xs is a list of int instances. Negative integers and
    booleans are accepted.
    """
    if not pre(xs):
        raise ValueError(f"Require list of integers (got xs={xs})")
    return [x for x in xs if x % 2 == 0]

# -- Tests --

from typing import Callable

def check(candidate: Callable[[List[int]], List[int]]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate([1, 2, 3, 4, 5, 6]) == [2, 4, 6]
    assert candidate([]) == []
    try:
        candidate([1, 2.5, 3])
    except ValueError:
        pass
    else:
        raise AssertionError('expected ValueError')
    assert candidate([1]) == []
    assert candidate([6]) == [6]
    return True

if __name__ == "__main__":
    assert check(prog), f"Failed: {__file__}"
    print("All tests passed.")
