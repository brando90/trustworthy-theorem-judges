"""Union-Find via quick-find component labels.

Edge cases:
- Empty structures have no valid element indices.
- Out-of-bounds finds return None.
- Out-of-bounds unions leave the structure unchanged.

"""

from typing import Callable, List, Optional


Labels = List[int]


def make_set(n: int) -> Labels:
    """For integer n, return the list of singleton labels 0 through n-1. Return an empty list when
    n <= 0.
    """
    if n < 0:
        return []
    return list(range(n))


def pre(labels: Labels) -> bool:
    """Return True exactly when labels is a list of int instances, each in 0..len(labels)-1.
    Booleans within that range and the empty list are accepted. No additional relationship
    between labels and their positions is required.
    """
    if not isinstance(labels, list):
        return False
    return all(isinstance(rep, int) and 0 <= rep < len(labels) for rep in labels)


def find(labels: Labels, x: int) -> Optional[int]:
    """Return labels[x] when x is an in-bounds int instance, including a boolean. Return None for
    non-integer or out-of-bounds x. Stored labels are returned without validation.
    """
    if not isinstance(x, int) or x < 0 or x >= len(labels):
        return None
    return labels[x]


def connected(labels: Labels, x: int, y: int) -> bool:
    """Return True when both indices resolve to non-None stored labels and those labels compare
    equal. Return False if either index is non-integer or out of bounds, or either stored label
    is None.
    """
    rx = find(labels, x)
    ry = find(labels, y)
    return rx is not None and ry is not None and rx == ry


def union(labels: Labels, x: int, y: int) -> Labels:
    """Return a fresh list replacing every occurrence of y's stored label with x's stored label,
    leaving labels unchanged. If either index is non-integer or out of bounds, or either stored
    label is None, return an unchanged copy.
    """
    rx = find(labels, x)
    ry = find(labels, y)
    if rx is None or ry is None:
        return list(labels)
    return [rx if rep == ry else rep for rep in labels]


def check(candidate: Callable[[Labels, int, int], Labels]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate([0, 1, 2, 3], 0, 1) == [0, 0, 2, 3]
    assert candidate([0, 0, 2], 1, 2) == [0, 0, 0]
    assert candidate([], 0, 1) == []
    assert candidate([], 0, 0) == []
    assert candidate([0], 1, 1) == [0]
    return True


if __name__ == "__main__":
    assert check(union), f"Failed: {__file__}"
    print("All tests passed.")
