# Synthetic VeriBench task -- Inspired by: models C++/Rust move discipline preventing double-move/use-after-move.
# Original language: Python
# Category: memory_bugs
"""Return whether an owned value can move from a valid source into an empty destination."""

from typing import Callable


def pre_condition(src_valid, dst_empty) -> bool:
    """Return whether src_valid and dst_empty are nonnegative integers and dst_empty is one of 0, 1
    and src_valid is one of 0, 1.
    """
    return isinstance(src_valid, int) and src_valid >= 0 and isinstance(dst_empty, int) and dst_empty >= 0 and dst_empty in (0, 1) and src_valid in (0, 1)


def my_owned_move_allowed(src_valid, dst_empty) -> bool:
    """Return whether an owned value can move from a valid source into an empty destination. Raise
    AssertionError if the input predicate rejects the arguments.
    """
    assert pre_condition(src_valid, dst_empty), "pre violated"
    return src_valid == 1 and dst_empty == 1


def _must_raise_assertion(thunk: Callable[[], object]) -> None:
    """Call thunk once. Return None if it raises AssertionError. Raise AssertionError if it returns
    normally. Other exceptions propagate.
    """
    try:
        thunk()
    except AssertionError:
        return
    raise AssertionError("expected AssertionError")


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(1, 1) is True
    assert candidate(0, 1) is False
    assert candidate(0, 0) is False
    _must_raise_assertion(lambda: candidate(-1, 1))
    assert candidate(1, 0) is False
    return True


if __name__ == "__main__":
    assert check(my_owned_move_allowed)
    print(f"All tests passed: {__file__}!")
