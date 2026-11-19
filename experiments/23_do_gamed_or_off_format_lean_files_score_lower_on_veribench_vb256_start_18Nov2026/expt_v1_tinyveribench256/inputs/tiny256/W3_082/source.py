"""Allow request only when request_origin == page_origin.

Teaching model for MIT 6.858.
"""


def safe_same_origin(request_origin: int, page_origin: int) -> bool:
    """Allow request only when request_origin == page_origin."""
    return request_origin == page_origin


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(100, 100) == True
    assert candidate(100, 200) == False
    assert candidate(0, 999) == False
    assert candidate(0, 0) == True
    assert candidate(42, 43) == False
    return True


assert check(safe_same_origin), "Candidate failed tests"
print("All tests passed.")
