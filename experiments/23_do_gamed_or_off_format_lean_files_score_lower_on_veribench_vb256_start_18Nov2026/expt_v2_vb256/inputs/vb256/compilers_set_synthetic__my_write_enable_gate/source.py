# Synthetic VeriBench task — Inspired by: conditional store write-enable gate
# Original language: Python
# Category: 12_compilers
# Lines: generated
"""Return newval when enabled is truthy, otherwise oldval."""

from typing import Callable


def pre_condition(oldval: int, newval: int, enabled: bool) -> bool:
    """Return whether oldval and newval are nonnegative int instances. Booleans qualify as int
    instances. enabled is not checked.
    """
    return isinstance(oldval, int) and oldval >= 0 and isinstance(newval, int) and newval >= 0


def my_write_enable_gate(oldval: int, newval: int, enabled: bool) -> int:
    """Return newval if enabled is truthy, otherwise oldval. Raise AssertionError if either value
    is not a nonnegative int instance.
    """
    assert pre_condition(oldval, newval, enabled), 'pre violated'
    return newval if enabled else oldval


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(5, 9, True) == 9
    assert candidate(5, 9, False) == 5
    assert candidate(0, 0, True) == 0
    assert candidate(100, 200, False) == 100
    assert candidate(3, 7, True) == 7
    return True


if __name__ == '__main__':
    assert check(my_write_enable_gate)
    print(f'All tests passed: {__file__}!')
