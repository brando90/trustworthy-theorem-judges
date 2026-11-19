"""Logical-bound-checked list access. Negative indices and indices at least size raise ValueError.
Other indices use ordinary list indexing and may raise IndexError. Includes a power-of-two
helper and fixed checks.
"""

from typing import Callable


def _next_power_of_two(n: int) -> int:
    """Return the smallest power of 2 >= n (minimum 1)."""
    if n <= 1:
        return 1
    p = 1
    while p < n:
        p <<= 1
    return p


def safe_baggy_get(buf: list, size: int, index: int):
    """Return buf[index] when 0 <= index < size and the element exists. Raise ValueError for
    negative indices or indices at least size. If an index passes that check but exceeds the
    list length, raise IndexError.
    """
    if index < 0 or index >= size:
        raise ValueError(
            f"index {index} out of logical bounds [0, {size}): "
            "baggy-bounds violation prevented"
        )
    return buf[index]


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate([10, 20, 30], 3, 0) == 10
    assert candidate([10, 20, 30], 3, 2) == 30
    assert candidate([99], 1, 0) == 99
    assert candidate([0, 1, 2, 3], 4, 3) == 3
    assert candidate([0], 3, 0) == 0
    return True


if __name__ == "__main__":
    assert check(safe_baggy_get), f"Failed: {__file__}"
    print("All tests passed.")
