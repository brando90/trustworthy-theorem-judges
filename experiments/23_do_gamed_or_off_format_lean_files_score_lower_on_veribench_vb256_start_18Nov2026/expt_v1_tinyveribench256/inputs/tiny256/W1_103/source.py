# File: humaneval_34_unique.py
# HumanEval problem HumanEval/34

"""Sorted list of the distinct elements of a list, with unit tests."""

def unique(l: list):
    """Return a new sorted list of distinct elements. Elements must be hashable and sortable
    together. Unhashable elements or unsupported ordering comparisons raise TypeError.
    """
    return sorted(list(set(l)))

# Test function


METADATA = {}


def check(candidate):
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert candidate([]) == []
    assert candidate([4, 1, 4]) == [1, 4]
    assert candidate([5, 3, 5, 2, 3, 3, 9, 0, 123]) == [0, 2, 3, 5, 9, 123]
    assert candidate([0]) == [0]
    assert candidate([1]) == [1]



# Run tests
if __name__ == "__main__":
    check(unique)
    print("All tests passed!")
