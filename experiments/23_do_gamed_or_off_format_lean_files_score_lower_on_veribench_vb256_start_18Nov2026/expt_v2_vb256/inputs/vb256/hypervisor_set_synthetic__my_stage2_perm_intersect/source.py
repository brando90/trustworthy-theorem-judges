# Synthetic VeriBench task — Inspired by: stage-1 and stage-2 EPT/IOMMU permission intersection
# Original language: Python
# Category: 11_hypervisor
# Lines: generated
"""Return True when every bit requested in op is permitted by both stage1 and stage2."""

from typing import Callable


def pre_condition(stage1: int, stage2: int, op: int) -> bool:
    """Return whether stage1, stage2 and op are integers and 0 ≤ stage1 ≤ 1000000 and 0 ≤ stage2 ≤
    1000000 and 0 ≤ op ≤ 1000000.
    """
    return isinstance(stage1, int) and 0 <= stage1 <= 1000000 and isinstance(stage2, int) and 0 <= stage2 <= 1000000 and isinstance(op, int) and 0 <= op <= 1000000


def my_stage2_perm_intersect(stage1: int, stage2: int, op: int):
    """Return True when every bit requested in op is permitted by both stage1 and stage2. A zero
    mask requests no permissions. All three masks must be integers from 0 through 1,000,000, or
    the function raises AssertionError.
    """
    assert pre_condition(stage1, stage2, op), 'pre violated'
    return (op & stage1) == op and (op & stage2) == op


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(7, 7, 5) is True
    assert candidate(7, 1, 1) is True
    assert candidate(3, 7, 2) is True
    assert candidate(7, 0, 1) is False
    try:
        candidate(-1, 7, 5)
    except AssertionError:
        pass
    else:
        raise AssertionError('expected AssertionError')
    return True


if __name__ == '__main__':
    assert check(my_stage2_perm_intersect)
    print(f'All tests passed: {__file__}!')
