"""Model a namespace visibility decision by returning True for every input, including missing PIDs
and empty mappings.
"""


def unsafe_namespace_resolve(process_ns: int, pid: int,
                              pid_ns_map: dict[int, int]) -> bool:
    """Return True unconditionally. Ignore process_ns, pid, and pid_ns_map, including whether the
    PID exists in the mapping.
    """
    return True  # namespace never checked — vulnerability


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(1, 100, {1: 0, 2: 0, 100: 1, 101: 1, 200: 2}) is True
    assert candidate(1, 1, {1: 0, 2: 0, 100: 1, 101: 1, 200: 2}) is True
    assert candidate(1, 200, {1: 0, 2: 0, 100: 1, 101: 1, 200: 2}) is True
    assert candidate(1, 9999, {1: 0, 2: 0, 100: 1, 101: 1, 200: 2}) is True
    assert candidate(1, 100, {}) is True
    return True


assert check(unsafe_namespace_resolve), "Candidate failed namespace isolation tests"
print("All tests passed.")
