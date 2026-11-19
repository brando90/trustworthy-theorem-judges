"""Report path feasibility: only checks upper > 0; lower bound ignored.

Teaching model for MIT 6.858.
"""


def unsafe_constraint_solve(lower: int, upper: int) -> bool:
    """Return True exactly when upper > 0, ignoring lower. Return False for zero or negative upper
    bounds. This is a toy feasibility flag, not a check that the interval from lower to upper is
    nonempty.
    """
    # Vulnerability: lower bound is never consulted.
    return upper > 0


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(0, 10) is True
    assert candidate(3, 7) is True
    assert candidate(10, 3) is True
    assert candidate(5, 5) is True
    assert candidate(0, 0) is False
    return True


assert check(unsafe_constraint_solve), "Candidate failed tests"
print("All tests passed.")
