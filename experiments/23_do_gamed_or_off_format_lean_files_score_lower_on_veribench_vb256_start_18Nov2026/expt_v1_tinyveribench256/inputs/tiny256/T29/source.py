# Safe setuid: allows privilege change only when caller is root (uid == 0).

"""Returns True only when current_uid is root (0)."""

def safe_setuid(current_uid: int, target_uid: int) -> bool:
    """Return True when current_uid equals zero, otherwise False, regardless of target_uid. This
    function only evaluates the supplied identifier. It does not inspect or change process
    credentials.
    """
    return current_uid == 0


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_setuid(0, 1000) == True
    assert safe_setuid(0, 0) == True
    assert safe_setuid(1001, 0) == False
    assert safe_setuid(1001, 1002) == False
    assert safe_setuid(0, 1) is True

if __name__ == "__main__":
    check()
