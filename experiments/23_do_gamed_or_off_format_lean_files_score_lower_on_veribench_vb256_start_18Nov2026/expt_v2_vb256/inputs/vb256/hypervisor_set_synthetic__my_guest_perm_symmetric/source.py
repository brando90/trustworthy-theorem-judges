# Synthetic VeriBench task — Inspired by: XOR-masked permission agreement gate
# Original language: Python
# Category: 11_hypervisor
# Lines: generated
"""Return whether the requested and granted permission words agree on every bit selected by mask."""

from typing import Callable


def pre_condition(perm: int, granted: int, mask: int) -> bool:
    """Return whether perm and granted are nonnegative integers and mask is a positive integer.
    Boolean values also satisfy these integer checks.
    """
    return isinstance(perm, int) and perm >= 0 and isinstance(granted, int) and granted >= 0 and isinstance(mask, int) and mask > 0


def my_guest_perm_symmetric(perm: int, granted: int, mask: int) -> bool:
    """Return whether the requested and granted permission words agree on every bit selected by
    mask.

    Raise AssertionError when pre_condition rejects the arguments.
    """
    assert pre_condition(perm, granted, mask), 'pre violated'
    return ((perm ^ granted) & mask) == 0


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(3, 3, 1) == True
    assert candidate(7, 7, 7) == True
    assert candidate(0, 1, 1) == False
    assert candidate(3, 5, 7) == False
    try:
        candidate(0, 0, 0)
    except AssertionError:
        pass
    else:
        raise AssertionError('expected AssertionError')
    return True


if __name__ == '__main__':
    assert check(my_guest_perm_symmetric)
    print(f'All tests passed: {__file__}!')
