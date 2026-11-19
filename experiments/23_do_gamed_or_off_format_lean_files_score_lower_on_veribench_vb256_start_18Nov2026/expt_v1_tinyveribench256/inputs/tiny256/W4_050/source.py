# Safe key persistence: encryption key only present in RAM when device is unlocked.

"""Returns True only when the device is unlocked and the key is present."""

def safe_key_persistence(device_locked: bool, key_present: bool) -> bool:
    """Return True when device_locked is False and key_present is True. Otherwise return False.
    This evaluates the supplied boolean flags without changing device or key state.
    """
    return (not device_locked) and key_present


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_key_persistence(False, True) == True
    assert safe_key_persistence(False, False) == False
    assert safe_key_persistence(True, False) == False
    assert safe_key_persistence(True, True) == False
    assert safe_key_persistence(device_locked=False, key_present=False) is False

if __name__ == "__main__":
    check()
