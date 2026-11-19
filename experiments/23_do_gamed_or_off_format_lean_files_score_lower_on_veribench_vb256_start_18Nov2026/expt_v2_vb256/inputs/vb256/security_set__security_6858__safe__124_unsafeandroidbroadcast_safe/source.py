# Safe Android broadcast intent: requires a receiver permission to protect sensitive broadcasts.

"""Returns True only when both a permission is required and the broadcast is protected."""

def safe_android_broadcast(permission_required: bool, broadcast_protected: bool) -> bool:
    """Return True exactly when both permission_required and broadcast_protected are True. These
    are supplied boolean flags. This predicate does not send a broadcast, inspect Android
    permissions, or enforce receiver restrictions.
    """
    return permission_required and broadcast_protected


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_android_broadcast(True, True) == True
    assert safe_android_broadcast(False, False) == False
    assert safe_android_broadcast(True, False) == False
    assert safe_android_broadcast(False, True) == False
    assert safe_android_broadcast(permission_required=False, broadcast_protected=False) is False

if __name__ == "__main__":
    check()
