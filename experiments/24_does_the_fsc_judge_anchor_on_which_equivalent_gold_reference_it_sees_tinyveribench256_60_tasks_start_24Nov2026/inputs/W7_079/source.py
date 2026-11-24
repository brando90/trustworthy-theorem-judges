"""Teaching model that returns whether hop is less than num_hops, without checking either integer
for nonnegativity.
"""

def unsafe_hop_read(num_hops: int, hop: int) -> bool:
    """Return True if hop < num_hops, otherwise False. No nonnegative-index check is performed."""
    return hop < num_hops


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(5, 5) is False
    assert candidate(5, 10) is False
    assert candidate(0, 0) is False
    assert candidate(20, 0) is True
    assert candidate(5, 0) is True
    return True


assert check(unsafe_hop_read), "Candidate failed hop-by-hop tests"
print("All tests passed.")
