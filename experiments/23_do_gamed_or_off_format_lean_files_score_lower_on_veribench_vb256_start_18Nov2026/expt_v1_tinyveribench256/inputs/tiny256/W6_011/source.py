"""Decide whether a system call is permitted — ignoring the filter entirely.

Teaching model for MIT 6.858.
"""


def unsafe_seccomp_filter(syscall_id: int, allowed: list[int]) -> bool:
    """Decide whether a system call is permitted — ignoring the filter entirely.

    The `allowed` list is accepted as a parameter but never consulted.
    Every system call is unconditionally allowed, so the filter provides
    zero isolation benefit.
    (MIT 6.858 Lecture 6: Firecracker uses seccomp-bpf to restrict which
    syscalls the VMM process itself can invoke, limiting blast radius if the
    VMM is compromised.)
    """
    return True  # filter never applied — vulnerability


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(1, [1, 2, 3, 60]) is True
    assert candidate(999, [1, 2, 3, 60]) is True
    assert candidate(1, []) is True
    assert candidate(0, []) is True
    assert candidate(4096, [1, 2, 3, 60]) is True
    return True


assert check(unsafe_seccomp_filter), "Candidate failed seccomp filter tests"
print("All tests passed.")
