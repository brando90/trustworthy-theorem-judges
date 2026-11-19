# Synthetic VeriBench task - Inspired by: embedded power-state transition guard: Active=0 Sleep=1 Off=2
# Original language: Python
# Category: os_embedded
"""Return whether the requested power-state change is one of 0 to 1, 1 to 0, or 1 to 2."""
from typing import Callable
def pre_condition(src: int, dst: int) -> bool:
    """Return whether 0 ≤ src ≤ 2 and 0 ≤ dst ≤ 2."""
    return 0 <= src <= 2 and 0 <= dst <= 2
def my_power_transition_ok(src: int, dst: int) -> bool:
    """Return whether (src, dst) is (0, 1), (1, 0), or (1, 2). Raise AssertionError unless both
    arguments are between 0 and 2 inclusive.
    """
    assert pre_condition(src, dst), "pre violated"
    return bool((src == 0 and dst == 1) or (src == 1 and dst == 0) or (src == 1 and dst == 2))
def _must_raise(call) -> None:
    """Return normally iff call() raises AssertionError; otherwise raise AssertionError."""
    try:
        call()
    except AssertionError:
        return
    raise AssertionError("expected precondition failure")
def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(0, 1) is True
    assert candidate(1, 0) is True
    assert candidate(1, 2) is True
    assert candidate(0, 2) is False
    _must_raise(lambda: candidate(-1, 0))
    return True

if __name__ == "__main__":
    assert check(my_power_transition_ok)
    print(f"All tests passed: {__file__}!")
