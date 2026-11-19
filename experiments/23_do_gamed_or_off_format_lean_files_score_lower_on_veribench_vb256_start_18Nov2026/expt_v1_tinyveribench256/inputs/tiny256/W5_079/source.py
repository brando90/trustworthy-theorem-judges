# Unsafe WEP keystream-reuse check: accepts packets without detecting IV reuse.

"""Approve the request without checking whether iv1 and iv2 are equal."""

def unsafe_wep_check(iv1: int, iv2: int) -> bool:
    """Approve the request without checking whether iv1 and iv2 are equal.

    MIT 6.858 Quiz 2, Fall 2013: Wireless / WEP keystream reuse.
    """
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_wep_check(5, 5) == True
    assert unsafe_wep_check(1, 2) == True
    assert unsafe_wep_check(0, 0) == True
    assert unsafe_wep_check(0, 5) is True
    assert unsafe_wep_check(5, 1) is True

if __name__ == "__main__":
    check()
