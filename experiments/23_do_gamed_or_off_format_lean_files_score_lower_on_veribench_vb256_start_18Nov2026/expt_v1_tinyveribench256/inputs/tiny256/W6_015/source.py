"""Decide whether a memory allocation request should be granted — ignoring the limit.

Teaching model for MIT 6.858.
"""


def unsafe_cgroup_memory(current_bytes: int, request_bytes: int,
                         limit_bytes: int) -> bool:
    """Decide whether a memory allocation request should be granted — ignoring the limit.

    `limit_bytes` is accepted as a parameter but never checked.  Every request is
    unconditionally granted, even if it would push the tenant far beyond its cgroup
    memory limit.
    (MIT 6.858 Lecture 6: Linux cgroups limit per-VM memory so one VM cannot
    monopolise all RAM on the host; omitting this check is the vulnerability.)
    """
    return True  # limit never enforced — vulnerability


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(100, 50, 200) is True
    assert candidate(100, 200, 150) is True
    assert candidate(0, 1, 0) is True
    assert candidate(200, 1, 200) is True
    assert candidate(0, 1000000000, 1024) is True
    return True


assert check(unsafe_cgroup_memory), "Candidate failed cgroup memory tests"
print("All tests passed.")
