"""Binary search over a sorted list of integers.

Edge cases:
- Empty list returns None.
- Non-integer elements or unsorted lists are invalid and raise ValueError.
"""

from typing import List, Optional, Callable

def pre(arr: List[int], target: int) -> bool:
    """True iff arr is a sorted list of ints and target is an int."""
    return (
        isinstance(arr, list)
        and all(isinstance(x, int) for x in arr)
        and all(arr[i] <= arr[i+1] for i in range(len(arr)-1))
        and isinstance(target, int)
    )

def binary_search(arr: List[int], target: int) -> Optional[int]:
    """Search an ascending list of integers. Return the first matching midpoint encountered, or
    None if the target is absent. With duplicates the midpoint need not be the first occurrence.
    Booleans count as integers. Invalid input raises ValueError.
    """
    if not pre(arr, target):
        raise ValueError("Require sorted List[int] and int target")
    if not arr:
        return None
    
    left, right = 0, len(arr) - 1
    
    while left <= right:
        mid = (left + right) // 2
        mid_val = arr[mid]
        
        if mid_val == target:
            return mid
        elif mid_val < target:
            left = mid + 1
        else:
            right = mid - 1
    
    return None

# -- Tests --
def check(candidate: Callable[[List[int], int], Optional[int]]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate([1, 2, 3, 4, 5], 1) == 0
    assert candidate([1, 2, 3, 4, 5], 3) == 2
    assert candidate([1, 2, 3, 4, 5], 5) == 4
    assert candidate([1, 2, 3, 4, 5], 0) is None
    try:
        candidate([3, 2, 1], 2)
    except ValueError:
        pass
    else:
        raise AssertionError('expected ValueError')
    return True

if __name__ == "__main__":
    assert check(binary_search), f"Failed: {__file__}"
    print("All tests passed.")
