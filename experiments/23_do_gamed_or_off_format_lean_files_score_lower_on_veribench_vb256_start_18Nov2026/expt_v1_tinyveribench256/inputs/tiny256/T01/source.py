# File: humaneval_20_find_closest_elements.py
# HumanEval problem HumanEval/20

"""Closest pair of numbers in a list, returned in sorted order, with unit tests."""

from typing import List, Tuple


def find_closest_elements(numbers: List[float]) -> Tuple[float, float]:
    """For at least two finite numbers, return a closest pair in ascending order. Equal distances
    keep the first pair encountered in input-index traversal. Return None for shorter lists.
    Non-finite values follow Python subtraction, absolute-value, comparison, and sorting
    behavior. They need not yield a meaningful closest pair.
    """
    closest_pair = None
    distance = None

    for idx, elem in enumerate(numbers):
        for idx2, elem2 in enumerate(numbers):
            if idx != idx2:
                if distance is None:
                    distance = abs(elem - elem2)
                    closest_pair = tuple(sorted([elem, elem2]))
                else:
                    new_distance = abs(elem - elem2)
                    if new_distance < distance:
                        distance = new_distance
                        closest_pair = tuple(sorted([elem, elem2]))

    return closest_pair

# Test function


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert candidate([1.0, 2.0, 3.9, 4.0, 5.0, 2.2]) == (3.9, 4.0)
    assert candidate([1.0, 2.0, 5.9, 4.0, 5.0]) == (5.0, 5.9)
    assert candidate([1.0, 2.0, 3.0, 4.0, 5.0, 2.2]) == (2.0, 2.2)
    assert candidate([1.0, 2.0, 3.0, 4.0, 5.0, 2.0]) == (2.0, 2.0)
    assert candidate([8.0, 4.0]) == (4.0, 8.0)



# Run tests
if __name__ == "__main__":
    check(find_closest_elements)
    print("All tests passed!")
