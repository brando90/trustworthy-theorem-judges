# Synthetic VeriBench task -- Inspired by: function-prologue stack-overflow guard with red zone.
# Original language: Python
# Category: memory_bugs
"""Stack headroom check before pushing a new frame onto a downward-growing stack."""

from typing import Callable

RED_ZONE_BYTES = 64


def pre_condition(stack_top, stack_base, frame_used) -> bool:
    """Return whether stack_top, stack_base and frame_used are nonnegative integers and stack_base
    ≤ stack_top.
    """
    return (
        isinstance(stack_top, int)
        and stack_top >= 0
        and isinstance(stack_base, int)
        and stack_base >= 0
        and isinstance(frame_used, int)
        and frame_used >= 0
        and stack_base <= stack_top
    )


def my_stack_headroom_ok(stack_top, stack_base, frame_used) -> bool:
    """For nonnegative Python integers, return whether stack_base + frame_used + RED_ZONE_BYTES is
    at most stack_top; RED_ZONE_BYTES is 64. Raise AssertionError for rejected arguments. A
    stack_base greater than stack_top returns False. This computes a headroom predicate without
    changing stack state.
    """
    if not (
        isinstance(stack_top, int)
        and stack_top >= 0
        and isinstance(stack_base, int)
        and stack_base >= 0
        and isinstance(frame_used, int)
        and frame_used >= 0
    ):
        raise AssertionError("pre violated")
    return stack_base + frame_used + RED_ZONE_BYTES <= stack_top


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
    assert candidate(4096, 1024, 1024) is True
    assert candidate(1024, 1024, 0) is False
    assert candidate(100, 0, 36) is True
    assert candidate(100, 0, 37) is False
    _must_raise_assertion(lambda: candidate(-1, 0, 0))
    return True


if __name__ == "__main__":
    assert check(my_stack_headroom_ok)
    print(f"All tests passed: {__file__}!")
