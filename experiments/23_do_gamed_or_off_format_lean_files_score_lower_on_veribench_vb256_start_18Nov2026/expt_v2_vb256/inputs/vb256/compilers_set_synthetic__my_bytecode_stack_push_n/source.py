# Synthetic VeriBench task — Inspired by: push-n stack-depth effect with clamping
# Original language: Python
# Category: 12_compilers
# Lines: generated
"""Bytecode Stack Push N: depth after pushing n items, clamped to maxDepth."""

from typing import Callable


def pre_condition(depth: int, n: int, max_depth: int) -> bool:
    """Return whether max_depth is a positive Python integer, depth <= max_depth, and n >= 0.
    Booleans qualify as integers. Depth and n have no explicit type checks, and depth may be
    negative. Unsupported comparisons can raise TypeError.
    """
    return isinstance(max_depth, int) and max_depth > 0 and depth <= max_depth and n >= 0


def my_bytecode_stack_push_n(depth: int, n: int, max_depth: int) -> int:
    """Return depth + n if that sum is at most max_depth. Otherwise return max_depth. No stack is
    mutated. Negative depth and noninteger numeric depth or n can be accepted. Raise
    AssertionError when pre_condition rejects the arguments. Unsupported comparisons or addition
    can raise TypeError.
    """
    assert pre_condition(depth, n, max_depth), 'pre violated'
    return depth + n if depth + n <= max_depth else max_depth


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(2, 3, 10) == 5
    assert candidate(8, 5, 10) == 10
    assert candidate(0, 0, 5) == 0
    assert candidate(10, 0, 10) == 10
    try:
        candidate(0, 0, 0)
    except AssertionError:
        pass
    else:
        raise AssertionError('expected AssertionError')
    return True


if __name__ == '__main__':
    assert check(my_bytecode_stack_push_n)
    print(f'All tests passed: {__file__}!')
