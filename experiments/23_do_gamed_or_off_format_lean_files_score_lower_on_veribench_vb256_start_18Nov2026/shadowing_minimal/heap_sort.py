def heap_sort(xs: list[int]) -> list[int]:
    """Return the elements of xs in nondecreasing order."""
    import heapq
    h = list(xs); heapq.heapify(h)
    return [heapq.heappop(h) for _ in range(len(h))]
