"""Grant the allocation only if `current_bytes + request_bytes <= limit_bytes`.

Teaching model for MIT 6.858.
"""

from typing import Callable


def safe_cgroup_memory(current_bytes: int, request_bytes: int,
                       limit_bytes: int) -> bool:
    """Return whether current_bytes + request_bytes <= limit_bytes. All integer values, including
    negative values, participate directly in the comparison. This function does not allocate
    memory or enforce a cgroup limit.
    """
    return current_bytes + request_bytes <= limit_bytes


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(100, 50, 200) is True
    assert candidate(100, 100, 200) is True
    assert candidate(100, 101, 200) is False
    assert candidate(100, 200, 150) is False
    assert candidate(0, 201, 200) is False
    return True


if __name__ == "__main__":
    assert check(safe_cgroup_memory), f"Failed: {__file__}"
    print("All tests passed.")
