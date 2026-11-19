"""
Return the high median of data.

When the number of data points is odd, the middle value is returned.
When it is even, the larger of the two middle values is returned.

Sourced from Python's standard `statistics` library.

Reference:
https://github.com/python/cpython/blob/main/Lib/statistics.py
See function: median_high (around line 498)
"""

from typing import Callable, Any, List
import numbers

# -- Pre-condition --
def pre(data: Any) -> bool:
    """Return True exactly for nonempty lists or tuples whose elements are instances of
    numbers.Number. Ordering compatibility is not checked.
    """
    if not isinstance(data, (list, tuple)):
        return False
    if not data:
        return False
    return all(isinstance(x, numbers.Number) for x in data)

# -- Implementation --

class StatisticsError(ValueError):
    """ValueError raised for invalid statistics input, such as empty data."""
    pass

def median_high(data: List[numbers.Number]) -> numbers.Number:
    """Return the high median of data.

    When the number of data points is odd, the middle value is returned.
    When it is even, the larger of the two middle values is returned.

    Raise StatisticsError when the dataset is empty.
    """
    data = sorted(data)
    n = len(data)
    if n == 0:
        raise StatisticsError("no median for empty data")
    return data[n // 2]

# Main function to be verified
def benchmark_median_high(data: List[numbers.Number]) -> numbers.Number:
    """Return the upper middle element after sorting a nonempty list or tuple of numbers.Number
    instances. Raise StatisticsError when that validation fails. Sorting errors propagate.
    """
    if not pre(data):
        raise StatisticsError("benchmark_median_high requires a non-empty list/tuple of numbers")
    return median_high(data)

# -- Tests --

def check(candidate: Callable[[list], Any]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate([1, 3, 5]) == 3
    assert candidate([1, 2, 3, 4, 5, 6, 9]) == 4
    assert candidate([1, 3, 5, 7]) == 5
    assert candidate([42]) == 42
    assert candidate([10, 20]) == 20
    return True

if __name__ == "__main__":
    assert check(benchmark_median_high), f"Failed: {__file__}"
    print("All tests passed.")
