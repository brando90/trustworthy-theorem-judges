"""Linear search for the first occurrence of a target in a list of naturals.

Edge cases:
- Empty lists return None.
- Duplicate targets return the first matching index.
- Inputs must be non-negative integers, each at least zero."""

from typing import Callable, List, Optional


def _is_nat(value: object) -> bool:
    """True iff value is a non-negative int and not a bool."""
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0


def pre(arr: List[int], target: int) -> bool:
    """Return whether arr is a list of nonnegative ints excluding bool and target is a nonnegative
    int excluding bool.
    """
    return (
        isinstance(arr, list)
        and all(_is_nat(x) for x in arr)
        and _is_nat(target)
    )


def linear_search(arr: List[int], target: int) -> Optional[int]:
    """Return the first matching index in a list of nonnegative integers, or None when absent.
    Non-integers, booleans and negative integers in either the list or the target raise
    ValueError.
    """
    if not pre(arr, target):
        raise ValueError("Require List[Nat] and Nat target")

    for idx, value in enumerate(arr):
        if value == target:
            return idx
    return None


def check(candidate: Callable[[List[int], int], Optional[int]]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate([4, 2, 7, 9], 7) == 2
    assert candidate([], 5) is None
    assert candidate([3, 1, 3, 5], 3) == 0
    assert candidate([9, 4, 9, 1], 1) == 3
    try:
        candidate([1, -1], 1)
    except ValueError:
        pass
    else:
        raise AssertionError('expected ValueError')
    return True


if __name__ == "__main__":
    assert check(linear_search), f"Failed: {__file__}"
    print("All tests passed.")
