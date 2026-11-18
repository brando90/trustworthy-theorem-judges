"""Compute n - 1 estimated quantile cut points from sorted data. Use n=4 for quartiles, 10 for
deciles, or 100 for percentiles. Inclusive estimates use the observed endpoints. Exclusive
estimates can extrapolate beyond them. Adapted from Python's statistics library.
"""

from typing import Callable, Any, List, Union, Literal
from fractions import Fraction
from decimal import Decimal

# -- Pre-condition --

def pre(data: Any, n: int = 4, method: str = 'exclusive') -> bool:
    """Return True exactly for a list or tuple with at least two elements, an int n >= 1, and
    method equal to 'inclusive' or 'exclusive'. Boolean n values follow int checks. Element
    types are not checked.
    """
    if not isinstance(data, (list, tuple)):
        return False
    if len(data) < 2:
        return False
    if not isinstance(n, int) or n < 1:
        return False
    if method not in ('inclusive', 'exclusive'):
        return False
    return True

# -- Implementation --

class StatisticsError(ValueError):
    """ValueError raised for invalid statistics input, such as too few data points or n < 1."""
    pass

def quantiles(data: List[Union[int, float, Fraction, Decimal]], 
              n: int = 4, 
              method: Literal['exclusive', 'inclusive'] = 'exclusive') -> List[Union[float, Fraction, Decimal]]:
    """Return n-1 estimated quantile cuts from sorted numeric data. N=1 returns []. Quartiles use
    n=4, deciles 10, percentiles 100. Inclusive uses endpoint ranks. Exclusive uses sample ranks
    and may extrapolate. Require integer n. Raise StatisticsError for n<1 or fewer than two
    observations, and ValueError for an unknown method.
    """
    if n < 1:
        raise StatisticsError('n must be at least 1')
    data = sorted(data)
    ld = len(data)
    if ld < 2:
        raise StatisticsError('must have at least two data points')
    
    if method == 'inclusive':
        m = ld - 1
        result = []
        for i in range(1, n):
            j, delta = divmod(i * m, n)
            interpolated = (data[j] * (n - delta) + data[j + 1] * delta) / n
            result.append(interpolated)
        return result
    
    if method == 'exclusive':
        m = ld + 1
        result = []
        for i in range(1, n):
            j = i * m // n                               # rescale i to m/n
            j = 1 if j < 1 else ld-1 if j > ld-1 else j  # clamp to 1 .. ld-1
            delta = i*m - j*n                            # exact integer math
            interpolated = (data[j - 1] * (n - delta) + data[j] * delta) / n
            result.append(interpolated)
        return result
    
    raise ValueError(f'Unknown method: {method!r}')

# Main function to be verified
def benchmark_quantiles(data: List[Union[int, float, Fraction, Decimal]], 
                        n: int = 4, 
                        method: Literal['exclusive', 'inclusive'] = 'exclusive') -> List[Union[float, Fraction, Decimal]]:
    """Return n-1 estimated quantile cuts via quantiles. Require a list or tuple of at least two
    elements, int n>=1, and method 'inclusive' or 'exclusive'. Otherwise raise StatisticsError.
    Sorting and arithmetic errors propagate. Exclusive estimates may extrapolate beyond the
    data. N=1 returns [].
    """
    if not pre(data, n, method):
        raise StatisticsError("benchmark_quantiles requires at least 2 data points, n >= 1, and valid method")
    return quantiles(data, n=n, method=method)

# -- Tests --

def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    from math import isclose

    result = candidate([1, 2, 3, 4, 5], n=2)
    assert isclose(result[0], 3.0, rel_tol=0.0, abs_tol=1e-09)
    result = candidate([1.5, 2.5, 3.5, 4.5], n=2)
    assert isclose(result[0], 3.0, rel_tol=0.0, abs_tol=1e-09)
    assert candidate([4, 8], n=1) == []
    assert candidate([1, 5, 9], n=2) == [5.0]
    assert candidate([0, 4, 8], n=4, method='inclusive') == [2.0, 4.0, 6.0]
    return True

if __name__ == "__main__":
    assert check(benchmark_quantiles), f"Failed: {__file__}"
    print("All tests passed.")
