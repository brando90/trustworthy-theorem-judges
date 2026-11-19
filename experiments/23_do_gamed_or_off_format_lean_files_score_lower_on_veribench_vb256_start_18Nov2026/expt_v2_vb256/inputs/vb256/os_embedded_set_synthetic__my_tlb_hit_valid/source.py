# Synthetic VeriBench task - Inspired by: TLB hit validity after invalidation
# Original language: Python
# Category: os_embedded
"""Return whether a translation-cache entry is mapped and has not been invalidated."""
from typing import Callable
def pre_condition(mapped: bool, invalidated: bool) -> bool:
    """Accept all arguments without validating their values."""
    return True
def my_tlb_hit_valid(mapped: bool, invalidated: bool) -> bool:
    """Return whether a translation-cache entry is mapped and has not been invalidated. Raise
    AssertionError if the input predicate rejects the arguments.
    """
    assert pre_condition(mapped, invalidated), "pre violated"
    return bool(mapped and not invalidated)
def _must_raise(call) -> None:
    """Return normally when call() raises AssertionError. Raise AssertionError if call() returns
    normally. Propagate other exceptions.
    """
    try:
        call()
    except AssertionError:
        return
    raise AssertionError("expected precondition failure")
def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(True, False) is True
    assert candidate(True, True) is False
    assert candidate(False, False) is False
    assert candidate(False, True) is False
    assert candidate(mapped=False, invalidated=False) is False
    return True

if __name__ == "__main__":
    assert check(my_tlb_hit_valid)
    print(f"All tests passed: {__file__}!")
