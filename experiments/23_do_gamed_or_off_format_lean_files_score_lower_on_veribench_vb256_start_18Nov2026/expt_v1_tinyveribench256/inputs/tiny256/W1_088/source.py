# File: humaneval_22_filter_integers.py
# HumanEval problem HumanEval/22

"""Keep only the integer values of a list of arbitrary Python values, with unit tests."""

from typing import List, Any


def filter_integers(values: List[Any]) -> List[int]:
    """Return the elements satisfying isinstance(x, int), including booleans and other int
    subclasses. Preserve their original objects, order, and repetitions. Discard all other
    elements.
    """
    return [x for x in values if isinstance(x, int)]

# Test function


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert candidate([]) == []
    assert candidate([4, {}, [], 23.2, 9, 'adasd']) == [4, 9]
    assert candidate([3, 'c', 3, 3, 'a', 'b']) == [3, 3, 3]
    assert candidate([0]) == [0]
    assert candidate([1]) == [1]


# Run tests
if __name__ == "__main__":
    check(filter_integers)
    print("All tests passed!")
