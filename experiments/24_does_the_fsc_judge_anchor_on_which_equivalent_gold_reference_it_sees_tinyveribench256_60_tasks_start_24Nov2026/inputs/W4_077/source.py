"""Report path feasibility: the interval [lower, upper) is non-empty iff lower < upper.

Teaching model for MIT 6.858.
"""


def safe_constraint_solve(lower: int, upper: int) -> bool:
    """Report path feasibility: the interval [lower, upper) is non-empty iff lower < upper."""
    return lower < upper


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(0, 10) is True
    assert candidate(3, 7) is True
    assert candidate(10, 3) is False
    assert candidate(5, 5) is False
    assert candidate(0, 0) is False
    return True


assert check(safe_constraint_solve), "Candidate failed tests"
print("All tests passed.")
