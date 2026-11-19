# Synthetic VeriBench task — Inspired by: quorum overlap rule R + W > N for replicated control planes
# Original language: Python
# Category: 14_critical_infra
"""Return an integer flag indicating whether reads + writes exceeds nodes. Inputs are non-negative
counts. Read and write counts are not restricted to the node count.
"""

from typing import Callable


def pre_condition(reads: int, writes: int, nodes: int) -> bool:
    """Inputs are non-negative operational counters."""
    return reads >= 0 and writes >= 0 and nodes >= 0


def my_consensus_quorum_read(reads: int, writes: int, nodes: int) -> int:
    """Return 1 if the requested read and write quorum sizes together exceed the node count, or 0
    otherwise.

    Raise AssertionError when pre_condition rejects the arguments.
    """
    assert pre_condition(reads, writes, nodes), "pre violated"
    return 1 if reads + writes > nodes else 0


def check(candidate: Callable[[int, int, int], int]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(3, 3, 5) == 1
    assert candidate(2, 2, 5) == 0
    assert candidate(2, 3, 5) == 0
    assert candidate(0, 3, 5) == 0
    assert candidate(3, 7, 5) == 1
    return True


if __name__ == "__main__":
    assert check(my_consensus_quorum_read)
    print(f"All tests passed: {__file__}!")
