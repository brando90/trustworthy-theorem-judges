"""Allow access only when both x < bound and y < bound.

Teaching model for MIT 6.858.
"""


def safe_dual_bound(x: int, y: int, bound: int) -> bool:
    """Allow access only when both x < bound and y < bound."""
    return x < bound and y < bound


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(3, 5, 10) == True
    assert candidate(3, 15, 10) == False
    assert candidate(12, 5, 10) == False
    assert candidate(9, 9, 10) == True
    assert candidate(0, 0, 0) == False
    return True


assert check(safe_dual_bound), "Candidate failed tests"
print("All tests passed.")
