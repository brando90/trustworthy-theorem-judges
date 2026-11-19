"""Return `lower` as a concrete witness in [lower, upper), or None if infeasible.

Teaching model for MIT 6.858.
"""

from typing import Optional


def safe_witness_gen(lower: int, upper: int) -> Optional[int]:
    """Return lower when lower < upper, otherwise None. The returned integer is a witness in
    [lower, upper). No additional constraints or bug-triggering behavior are checked.
    """
    if lower < upper:
        return lower  # concrete, immediately usable bug-triggering value
    return None


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(10, 3) is None
    assert candidate(5, 5) is None
    assert candidate(0, 1) == 0
    assert candidate(100, 50) is None
    assert candidate(0, 3) == 0
    return True


assert check(safe_witness_gen), "Candidate failed tests"
print("All tests passed.")
