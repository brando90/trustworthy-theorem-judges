# Synthetic VeriBench task — Inspired by: guest-to-shadow PTE consistency update
# Original language: Python
# Category: 11_hypervisor
# Lines: generated
"""Return old_shadow_perm when dirty is False. Otherwise return the bitwise AND of guest_perm and
old_shadow_perm.
"""

from typing import Callable


def pre_condition(guest_perm: int, old_shadow_perm: int, dirty: bool) -> bool:
    """Return whether guest_perm and old_shadow_perm are integers and dirty is Boolean and 0 ≤
    guest_perm ≤ 1000000 and 0 ≤ old_shadow_perm ≤ 1000000.
    """
    return isinstance(guest_perm, int) and 0 <= guest_perm <= 1000000 and isinstance(old_shadow_perm, int) and 0 <= old_shadow_perm <= 1000000 and isinstance(dirty, bool)


def my_shadow_pte_update(guest_perm: int, old_shadow_perm: int, dirty: bool):
    """Return the current shadow permissions when the page is clean. For a dirty page, return the
    bits shared by the guest and shadow permissions.

    Raise AssertionError when pre_condition rejects the arguments.
    """
    assert pre_condition(guest_perm, old_shadow_perm, dirty), 'pre violated'
    return (guest_perm & old_shadow_perm) if dirty else old_shadow_perm


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(7, 7, True) == 7
    assert candidate(1, 7, True) == 1
    assert candidate(0, 7, True) == 0
    assert candidate(0, 3, False) == 3
    try:
        candidate(-1, 7, True)
    except AssertionError:
        pass
    else:
        raise AssertionError('expected AssertionError')
    return True


if __name__ == '__main__':
    assert check(my_shadow_pte_update)
    print(f'All tests passed: {__file__}!')
