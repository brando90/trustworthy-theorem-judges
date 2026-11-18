# Unsafe password check without salt: identical passwords produce identical stored values, enabling rainbow-table attacks.

"""Returns True when pw equals stored, with no salt applied."""

def unsafe_saltless_check(pw: int, stored: int) -> bool:
    """Returns True when pw equals stored, with no salt applied."""
    return pw == stored


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_saltless_check(1234, 1234) == True
    assert unsafe_saltless_check(0, 0) == True
    assert unsafe_saltless_check(9999, 1234) == False
    assert unsafe_saltless_check(1, 0) is False
    assert unsafe_saltless_check(1, 1) is True

if __name__ == "__main__":
    check()
