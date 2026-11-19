# Unsafe Android broadcast intent: sends sensitive data via unprotected broadcast.

"""Approve the request without checking whether the broadcast exposes data to all apps."""

def unsafe_android_broadcast(permission_required: bool, broadcast_protected: bool) -> bool:
    """Approve the request without checking whether the broadcast exposes data to all apps.

    MIT 6.858 Fall 2011 Quiz 2: Android unprotected broadcast intent leaks todo items.
    """
    return True  # vulnerable: broadcast always sent without receiver permission


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_android_broadcast(True, True) == True
    assert unsafe_android_broadcast(False, False) == True
    assert unsafe_android_broadcast(True, False) == True
    assert unsafe_android_broadcast(False, True) == True
    assert unsafe_android_broadcast(permission_required=False, broadcast_protected=False) is True

if __name__ == "__main__":
    check()
