"""Selection sort for a list of integers.

Edge cases:
- Empty list returns empty list.
- Non-integer elements are invalid and raise ValueError.
"""
from typing import List, Callable

def pre(arr: List[int]) -> bool:
    """Return True exactly when arr is a list containing only int instances, including booleans.
    Empty lists are accepted.
    """
    return isinstance(arr, list) and all(isinstance(x, int) for x in arr)

def selection_sort(arr: List[int]) -> List[int]:
    """Return a new list containing arr's elements in ascending order using selection sort, leaving
    arr unchanged. Return a fresh empty list for empty input. Raise ValueError unless arr is a
    list of int instances, including booleans.
    """
    if not pre(arr):
        raise ValueError("Input must be List[int]")
    if not arr:
        return []
    
    result = arr.copy()
    n = len(result)
    
    for i in range(n):
        # Find the minimum element in the remaining unsorted array
        min_idx = i
        for j in range(i + 1, n):
            if result[j] < result[min_idx]:
                min_idx = j
        
        # Swap the found minimum element with the first element
        result[i], result[min_idx] = result[min_idx], result[i]
    
    return result

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
    assert check(selection_sort), f"Failed: {__file__}"
    print("All tests passed.")
