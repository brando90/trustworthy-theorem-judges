"""Return Python's floor quotient n // d when d is nonzero, or 0 when d is zero. A zero-divisor
result has no distinct error marker.
"""


def unsafe_divide(n: int, d: int):
    """Return n // d using Python floor division when d is nonzero. Return 0 when d is zero,
    without raising ZeroDivisionError or providing a distinct error marker.
    """
    if d == 0:
        return 0  # wrong: 0 is a valid quotient; caller cannot tell an error occurred
    return n // d


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(10, 2) == 5
    assert candidate(9, 3) == 3
    assert candidate(5, 0) == 0
    assert candidate(100, 0) == 0
    assert candidate(0, 1) == 0
    return True


assert check(unsafe_divide), "Candidate failed tests"
print("All tests passed.")
