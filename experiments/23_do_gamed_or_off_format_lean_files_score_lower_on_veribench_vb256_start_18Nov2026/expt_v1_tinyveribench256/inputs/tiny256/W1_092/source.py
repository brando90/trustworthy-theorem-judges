# File: humaneval_26_remove_duplicates.py
# HumanEval problem HumanEval/26

"""Remove every element that occurs more than once from a list of integers, keeping order, with unit tests."""

from typing import List


def remove_duplicates(numbers: List[int]) -> List[int]:
    """ From a list of integers, remove all elements that occur more than once.
    Keep order of elements left the same as in the input.

    Used e.g. to keep only the values that appear exactly once in a list of IDs or readings or to drop every repeated entry, not just the extra copies."""
    import collections
    c = collections.Counter(numbers)
    return [n for n in numbers if c[n] <= 1]

# Test function


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert candidate([]) == []
    assert candidate([1, 2, 3, 4]) == [1, 2, 3, 4]
    assert candidate([1, 2, 3, 2, 4, 3, 5]) == [1, 4, 5]
    assert candidate([0]) == [0]
    assert candidate([1]) == [1]


# Run tests
if __name__ == "__main__":
    check(remove_duplicates)
    print("All tests passed!")
