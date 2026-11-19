"""Toy speculative-read model returning (None, supplied integer), representing an architectural
failure and a cache observation. No memory access or privilege fault occurs.
"""
from typing import Optional, Tuple


def unsafe_meltdown_read(kernel_byte: int) -> Tuple[Optional[int], Optional[int]]:
    """Return (None, kernel_byte), representing an architectural failure and a cache observation
    containing the supplied integer. No memory access, fault, or byte-range validation occurs.
    """
    return (None, kernel_byte)


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    arch, cache = candidate(202)
    assert arch is None
    assert cache == 202
    assert candidate(0)[1] == 0
    assert candidate(255)[1] == 255
    assert candidate(1) == (None, 1)
    return True


assert check(unsafe_meltdown_read), "Candidate failed Meltdown leak tests"
print("All tests passed.")
