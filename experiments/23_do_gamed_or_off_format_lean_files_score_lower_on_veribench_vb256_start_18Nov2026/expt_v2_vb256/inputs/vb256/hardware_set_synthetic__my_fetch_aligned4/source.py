# Synthetic VeriBench task — Inspired by: instruction fetch 4-byte alignment
# Original language: Python
# Category: 09_hardware
"""RV32 instruction-fetch alignment checker: true iff the fetch address is 4-byte aligned."""

from typing import Callable


def pre_condition(addr: int) -> bool:
    """Return whether 0 ≤ addr < 4096."""
    return 0 <= addr < 4096


def my_fetch_aligned4(addr: int):
    """RV32 instruction-fetch alignment checker: true iff the fetch address is 4-byte aligned. Used
    e.g. to flag a misaligned instruction fetch, which an RV32 core without compressed
    instructions must trap, or to validate branch targets in an instruction-set simulator.

    The input check requires that 0 ≤ addr < 4096. A failed check raises AssertionError.
    """
    assert pre_condition(addr), "pre violated"
    return addr % 4 == 0


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(0) is True
    assert candidate(4) is True
    assert candidate(1020) is True
    assert candidate(1) is False
    assert candidate(4095) is False
    return True


if __name__ == "__main__":
    assert check(my_fetch_aligned4)
    print(f"All tests passed: {__file__}!")
