# Unsafe setuid: allows privilege escalation without checking caller is root.

"""Approve the request without checking whether current_uid is root (0)."""

def unsafe_setuid(current_uid: int, target_uid: int) -> bool:
    """Approve the request without checking whether current_uid is root (0).

    MIT 6.858 Quiz 1, Spring 2014: privilege escalation via setuid.
    """
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_setuid(0, 1000) == True
    assert unsafe_setuid(1001, 0) == True
    assert unsafe_setuid(1001, 1002) == True
    assert unsafe_setuid(0, 0) is True
    assert unsafe_setuid(1, 1) is True

if __name__ == "__main__":
    check()
