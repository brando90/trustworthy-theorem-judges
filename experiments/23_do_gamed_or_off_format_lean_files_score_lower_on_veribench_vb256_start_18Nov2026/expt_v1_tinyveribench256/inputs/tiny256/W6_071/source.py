"""Model timing for a square-and-multiply step without performing arithmetic. Return (None, 60) for
an input equal to 1 and (None, 10) otherwise. Cycle counts are simulated constants.
"""
from typing import Tuple


def unsafe_rsa_bit(bit: int) -> Tuple[None, int]:
    """Return (None, 60) when bit equals 1. Otherwise return (None, 10), including for nonbinary
    integers. These are simulated cycle counts. No squaring, multiplication, or exponentiation
    is performed.
    """
    if bit == 1:
        return (None, 60)
    else:
        return (None, 10)


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    _, c1 = candidate(1)
    assert c1 == 60
    _, c0 = candidate(0)
    assert c0 == 10
    assert candidate(2) == (None, 10)
    assert candidate(3) == (None, 10)
    assert candidate(7) == (None, 10)
    return True


assert check(unsafe_rsa_bit), "Candidate failed RSA timing-leak tests"
print("All tests passed.")
