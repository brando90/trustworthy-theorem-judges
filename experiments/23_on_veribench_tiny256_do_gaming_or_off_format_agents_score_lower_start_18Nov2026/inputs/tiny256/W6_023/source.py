"""Model an unchecked length decision by always returning True, ignoring skip and buf_size. No
bytes are processed.
"""


def unsafe_tainted_len(skip: int, buf_size: int) -> bool:
    """Return True for every skip and buf_size, including negative integers. Neither argument is
    inspected, and no bytes are processed.
    """
    return True  # skip not validated — vulnerability


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(5, 100) == True
    assert candidate(200, 100) == True
    assert candidate(100, 100) == True
    assert candidate(0, 0) == True
    assert candidate(999999, 1) == True
    return True


assert check(unsafe_tainted_len), "Candidate failed tests"
print("All tests passed.")
