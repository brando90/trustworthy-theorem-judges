"""Heap index functions and heap-structure predicates from CLRS 6.1."""

from typing import List


def _is_nat(value: object) -> bool:
    """True iff value is a non-negative int and not a bool."""
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0


def _check_nat(value: int, name: str = "value") -> None:
    """Return None for a nonnegative int excluding bool. Otherwise raise ValueError using name in
    the message.
    """
    if not _is_nat(value):
        raise ValueError(f"{name} must be a natural number")


def _check_nat_list(arr: List[int], name: str = "arr") -> None:
    """Return None if arr is a list of nonnegative ints excluding bool. Otherwise raise ValueError
    using name in the message.
    """
    if not isinstance(arr, list) or not all(_is_nat(x) for x in arr):
        raise ValueError(f"{name} must be List[Nat]")


def parent(i: int) -> int:
    """Index of the parent of node i in a 0-based heap (0 for the root)."""
    _check_nat(i, "i")
    return 0 if i == 0 else (i - 1) // 2


def left(i: int) -> int:
    """Index of the left child of node i in a 0-based heap."""
    _check_nat(i, "i")
    return 2 * i + 1


def right(i: int) -> int:
    """Index of the right child of node i in a 0-based heap."""
    _check_nat(i, "i")
    return 2 * i + 2


def is_max_heap(arr: List[int], heap_size: int) -> bool:
    """Return whether every nonroot element in arr[:heap_size] is at most its parent. Oversized
    heap_size values use the whole list. Empty prefixes return True. Raise ValueError unless arr
    contains nonnegative ints excluding bool and heap_size is such an int.
    """
    _check_nat_list(arr)
    _check_nat(heap_size, "heap_size")
    size = min(heap_size, len(arr))
    for i in range(1, size):
        if arr[parent(i)] < arr[i]:
            return False
    return True


def is_min_heap(arr: List[int], heap_size: int) -> bool:
    """Return whether every nonroot element in arr[:heap_size] is at least its parent. Oversized
    heap_size values use the whole list. Empty prefixes return True. Raise ValueError unless arr
    contains nonnegative ints excluding bool and heap_size is such an int.
    """
    _check_nat_list(arr)
    _check_nat(heap_size, "heap_size")
    size = min(heap_size, len(arr))
    for i in range(1, size):
        if arr[parent(i)] > arr[i]:
            return False
    return True


def heap_height(n: int) -> int:
    """Height of a heap with n nodes (floor of log2 n, and 0 for n = 0 or 1)."""
    _check_nat(n, "n")
    return 0 if n == 0 else n.bit_length() - 1


def is_leaf(i: int, heap_size: int) -> bool:
    """Return whether 2*i + 1 is at least heap_size. This also returns True for indices outside the
    heap. Raise ValueError unless both arguments are nonnegative ints excluding bool.
    """
    _check_nat(i, "i")
    _check_nat(heap_size, "heap_size")
    return left(i) >= heap_size


def check() -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert parent(0) == 0
    assert left(1) == 3
    assert right(0) == 2
    assert is_max_heap([23, 17, 14, 6, 13, 10, 1, 5, 7, 12], 10) is False
    try:
        is_max_heap([1, -1], 2)
    except ValueError:
        pass
    else:
        raise AssertionError('expected ValueError')
    return True


if __name__ == "__main__":
    assert check(), f"Failed: {__file__}"
    print("All tests passed.")
