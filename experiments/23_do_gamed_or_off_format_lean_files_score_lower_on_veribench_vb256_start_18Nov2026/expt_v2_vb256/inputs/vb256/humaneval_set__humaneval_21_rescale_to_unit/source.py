# File: humaneval_21_rescale_to_unit.py
# HumanEval problem HumanEval/21

"""Linear rescaling of a list of numbers onto the interval 0 to 1, with unit tests."""

from typing import List


def rescale_to_unit(numbers: List[float]) -> List[float]:
    """Return (x - min(numbers)) / (max(numbers) - min(numbers)) for each element, preserving input
    order. Empty input raises ValueError. A zero range raises ZeroDivisionError. Finite inputs
    with a finite, nonzero range map the minimum to 0 and maximum to 1. Non-finite arithmetic
    can produce NaNs.
    """
    min_number = min(numbers)
    max_number = max(numbers)
    return [(x - min_number) / (max_number - min_number) for x in numbers]

# Test function


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert candidate([2.0, 49.9]) == [0.0, 1.0]
    assert candidate([100.0, 49.9]) == [1.0, 0.0]
    assert candidate([1.0, 2.0, 3.0, 4.0, 5.0]) == [0.0, 0.25, 0.5, 0.75, 1.0]
    assert candidate([2.0, 1.0, 5.0, 3.0, 4.0]) == [0.25, 0.0, 1.0, 0.5, 0.75]
    assert candidate([3.0, -1.0, -1.0]) == [1.0, 0.0, 0.0]


# Run tests
if __name__ == "__main__":
    check(rescale_to_unit)
    print("All tests passed!")
