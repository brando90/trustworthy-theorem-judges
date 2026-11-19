# Unsafe direct routing — MIT 6.858 Lecture 19: Anonymous Communication (Tor)
# Sends message with source IP embedded in the header — anyone on the path can see origin.

"""Return (src_ip, dst_ip, msg) unchanged as a tuple."""

from typing import Optional


def unsafe_direct_route(src_ip: int, dst_ip: int, msg: int) -> tuple[int, int, int]:
    """Return (src_ip, dst_ip, msg) unchanged as a tuple, retaining the source identifier
    explicitly. This function performs no network transmission.
    """
    return (src_ip, dst_ip, msg)


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(15, 22, 19) == (15, 22, 19)
    assert candidate(0, 0, 0) == (0, 0, 0)
    assert candidate(1, 0, 0) == (1, 0, 0)
    assert candidate(1, 1, 1) == (1, 1, 1)
    assert candidate(15, 1, 19) == (15, 1, 19)
    return True


assert check(unsafe_direct_route)
print("All tests passed.")
