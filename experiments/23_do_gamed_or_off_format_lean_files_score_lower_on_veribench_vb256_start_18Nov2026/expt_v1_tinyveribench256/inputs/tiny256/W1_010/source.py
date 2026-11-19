"""Merge sort for a list of integers.

Edge cases:
- Empty or single-element list returns copy.
- Non-integer elements are invalid and raise ValueError.
"""
from typing import List, Callable

def pre(arr: List[int]) -> bool:
    """Return True exactly when arr is a list containing only int instances, including booleans.
    Empty lists are accepted.
    """
    return isinstance(arr, list) and all(isinstance(x, int) for x in arr)

def merge_sort(arr: List[int]) -> List[int]:
    """Return a new list containing arr's elements in ascending order using merge sort, leaving arr
    unchanged. Empty and singleton inputs also return copies. Raise ValueError unless arr is a
    list of int instances, including booleans.
    """
    if not pre(arr):
        raise ValueError("Input must be List[int]")
    if len(arr) <= 1:
        return arr.copy()
    
    def merge(left: List[int], right: List[int]) -> List[int]:
        """Merge two sorted lists into a single sorted list."""
        result = []
        i = j = 0
        
        while i < len(left) and j < len(right):
            if left[i] <= right[j]:
                result.append(left[i])
                i += 1
            else:
                result.append(right[j])
                j += 1
        
        # Add remaining elements
        result.extend(left[i:])
        result.extend(right[j:])
        
        return result
    
    # Divide the array into halves
    mid = len(arr) // 2
    left = merge_sort(arr[:mid])
    right = merge_sort(arr[mid:])
    
    # Merge the sorted halves
    return merge(left, right)

# -- Tests --
def check(candidate: Callable[[List[int]], List[int]]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate([3, 1, 2]) == [1, 2, 3]
    assert candidate([]) == []
    assert candidate([1]) == [1]
    assert candidate([5, 2, 4, 6, 1, 3]) == [1, 2, 3, 4, 5, 6]
    try:
        candidate([1, 2.5])
    except ValueError:
        pass
    else:
        raise AssertionError('expected ValueError')
    return True

if __name__ == "__main__":
    assert check(merge_sort), f"Failed: {__file__}"
    print("All tests passed.")
