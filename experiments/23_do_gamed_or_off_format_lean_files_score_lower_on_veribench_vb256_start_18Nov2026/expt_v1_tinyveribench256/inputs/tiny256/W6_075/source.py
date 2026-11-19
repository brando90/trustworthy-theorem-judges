# Unsafe TCP ISN generation: predictable sequence by incrementing previous ISN.

"""Return the previous TCP initial sequence number plus 64."""

def unsafe_tcp_isn(prev_isn: int, connection_id: int) -> int:
    """Return the previous TCP initial sequence number plus 64. The supplied connection identifier
    is ignored.
    """
    return prev_isn + 64


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(1000, 1) == 1064
    assert candidate(5000, 10) == 5064
    assert candidate(0, 0) == 64
    assert candidate(100, 0) == 164
    assert candidate(4294967196, 1) == 4294967260
    return True


if __name__ == "__main__":
    assert check(unsafe_tcp_isn)
    print("All tests passed.")
