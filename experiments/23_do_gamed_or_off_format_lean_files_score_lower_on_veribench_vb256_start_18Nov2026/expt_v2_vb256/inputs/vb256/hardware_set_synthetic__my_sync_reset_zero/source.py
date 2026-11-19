# Synthetic VeriBench task — Inspired by: synchronous reset mux
# Original language: Python
# Category: 09_hardware
"""Register next-state mux with synchronous reset-to-zero behavior."""

from typing import Callable


def pre_condition(reset: bool, next_state: int) -> bool:
    """Return whether reset is Boolean and 0 ≤ next_state < 256."""
    return isinstance(reset, bool) and 0 <= next_state < 256


def my_sync_reset_zero(reset: bool, next_state: int):
    """Return 0 when reset is True. Otherwise return next_state unchanged. Require reset to be
    Boolean and 0 ≤ next_state < 256. A failed check raises AssertionError. The range check does
    not require next_state to be an integer. This function computes a value without storing
    state.
    """
    assert pre_condition(reset, next_state), "pre violated"
    return 0 if reset else next_state


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(True, 99) == 0
    assert candidate(True, 0) == 0
    assert candidate(False, 99) == 99
    assert candidate(False, 255) == 255
    assert candidate(False, 0) == 0
    return True


if __name__ == "__main__":
    assert check(my_sync_reset_zero)
    print(f"All tests passed: {__file__}!")
