"""
Calculates the median (middle value) of data.

Sourced from Python's standard `statistics` library.
"""

from typing import Callable, Any, List
from fractions import Fraction
from decimal import Decimal
import numbers

# -- Pre-condition --
def pre(data: Any) -> bool:
    """Return whether data is a nonempty list or tuple whose elements are numbers.Number instances.
    Do not check ordering or arithmetic compatibility. Complex values can pass.
    """
    if not isinstance(data, (list, tuple)):
        return False
    if not data:
        return False
    return all(isinstance(x, numbers.Number) for x in data)

# -- Implementation --

class StatisticsError(ValueError):
    """ValueError subclass raised when a statistics function gets empty or invalid data."""
    pass

def median(data: List[numbers.Number]) -> numbers.Number:
    """Sort data and return its middle value for odd length, or the sum of its two middle values
    divided by two for even length. Raise StatisticsError for empty data. Sorting and arithmetic
    errors propagate.
    """
    data = sorted(data)
    n = len(data)
    if n == 0:
        raise StatisticsError("no median for empty data")
    if n % 2 == 1:
        return data[n // 2]
    else:
        i = n // 2
        return (data[i - 1] + data[i]) / 2

# Main function to be verified
def benchmark_median(data: List[numbers.Number]) -> numbers.Number:
    """Return the median: the middle sorted value for odd length, or the average of the two middle
    values for even length. Raise StatisticsError unless data is a nonempty list or tuple of
    numbers.Number instances. Sorting and arithmetic errors propagate.
    """
    if not pre(data):
        raise StatisticsError("benchmark_median requires a non-empty list/tuple of numbers")
    return median(data)

# -- Tests --

def check(candidate: Callable[[list], Any]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate([1, 2, 3, 4, 5, 6, 9]) == 4
    assert candidate([1, 2, 3, 4, 5, 6]) == 3.5
    assert candidate([1, 3, 5, 7]) == 4.0
    assert candidate([42]) == 42
    assert candidate([9, 1, 6, 2, 5, 4, 3]) == 4
    return True

if __name__ == "__main__":
    assert check(benchmark_median), f"Failed: {__file__}"
    print("All tests passed.")
