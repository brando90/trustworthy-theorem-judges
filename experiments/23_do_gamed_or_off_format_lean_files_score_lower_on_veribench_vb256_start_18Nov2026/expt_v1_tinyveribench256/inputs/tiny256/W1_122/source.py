# File: humaneval_9_rolling_max.py
# HumanEval problem HumanEval/9

"""Rolling (prefix) maximum of a list of integers, with unit tests."""

from typing import List, Tuple


def rolling_max(numbers: List[int]) -> List[int]:
    """ From a given list of integers, generate a list of rolling maximum element found until given moment
    in the sequence.

    Used e.g. to track the running peak of a series such as the highest price or temperature seen so far or to build a prefix-maximum array in algorithms."""
    running_max = None
    result = []

    for n in numbers:
        if running_max is None:
            running_max = n
        else:
            running_max = max(running_max, n)

        result.append(running_max)

    return result

# Test function


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert candidate([]) == []
    assert candidate([1, 2, 3, 4]) == [1, 2, 3, 4]
    assert candidate([4, 3, 2, 1]) == [4, 4, 4, 4]
    assert candidate([3, 2, 3, 100, 3]) == [3, 3, 3, 100, 100]
    assert candidate([0]) == [0]


# Run tests
if __name__ == "__main__":
    check(rolling_max)
    print("All tests passed!")
