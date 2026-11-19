# Synthetic VeriBench task — Inspired by: stage-indexed measurement chain extension
# Original language: Python
# Category: 11_hypervisor
# Lines: generated
"""Return the updated one-byte boot measurement."""

from typing import Callable


def pre_condition(prev_measure: int, image_measure: int, stage: int) -> bool:
    """Return whether prev_measure, image_measure and stage are integers and 0 ≤ prev_measure ≤
    1000000 and 0 ≤ image_measure ≤ 1000000 and 0 ≤ stage ≤ 1000000.
    """
    return isinstance(prev_measure, int) and 0 <= prev_measure <= 1000000 and isinstance(image_measure, int) and 0 <= image_measure <= 1000000 and isinstance(stage, int) and 0 <= stage <= 1000000


def my_boot_measure_extend(prev_measure: int, image_measure: int, stage: int):
    """Return the updated one-byte boot measurement. Weight the previous measurement by 167, the
    image measurement by 13, add the stage number, and reduce modulo 256.

    Raise AssertionError when pre_condition rejects the arguments.
    """
    assert pre_condition(prev_measure, image_measure, stage), 'pre violated'
    return (prev_measure * 167 + image_measure * 13 + stage) % 256


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(0, 0, 0) == 0
    assert candidate(0, 1, 0) == 13
    assert candidate(1, 0, 0) == 167
    assert candidate(1, 1, 1) == 181
    try:
        candidate(-1, 0, 0)
    except AssertionError:
        pass
    else:
        raise AssertionError('expected AssertionError')
    return True


if __name__ == '__main__':
    assert check(my_boot_measure_extend)
    print(f'All tests passed: {__file__}!')
