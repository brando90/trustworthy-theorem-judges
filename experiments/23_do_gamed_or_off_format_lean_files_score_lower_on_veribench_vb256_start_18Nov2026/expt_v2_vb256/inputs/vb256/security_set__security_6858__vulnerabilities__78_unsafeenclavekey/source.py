# Unsafe enclave key: allows any software level to directly read the hardware UID key.

"""Return True without consulting the software privilege level."""

def unsafe_key_readable(software_level: int) -> bool:
    """Return True without consulting the software privilege level."""
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_key_readable(0) == True
    assert unsafe_key_readable(1) == True
    assert unsafe_key_readable(2) == True
    assert unsafe_key_readable(99) == True
    assert unsafe_key_readable(1000) == True

if __name__ == "__main__":
    check()
