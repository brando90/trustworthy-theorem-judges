"""Accept value if value >= low, ignoring the upper bound high.

Teaching model for MIT 6.858.
"""


def unsafe_range_check(value: int, low: int, high: int) -> bool:
    """Accept value if value >= low, ignoring the upper bound high."""
    return value >= low  # high (upper bound) ignored — vulnerability


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(5, 0, 10) == True
    assert candidate(15, 0, 10) == True
    assert candidate(0, 5, 10) == False
    assert candidate(5, 5, 10) == True
    assert candidate(1000, 0, 100) == True
    return True


assert check(unsafe_range_check), "Candidate failed tests"
print("All tests passed.")
