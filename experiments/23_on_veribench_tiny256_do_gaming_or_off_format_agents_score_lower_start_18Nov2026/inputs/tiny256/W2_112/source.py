# Safe null pointer dereference check: rejects null (0) pointer values.

"""Returns True only when ptr_val is non-zero (non-null)."""

def safe_ptr_check(ptr_val: int) -> bool:
    """Return False for ptr_val == 0 and True for every other integer, including negative values.
    This numeric guard does not dereference memory or verify that a nonzero address is valid.
    """
    return ptr_val != 0


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_ptr_check(1) == True
    assert safe_ptr_check(3735928559) == True
    assert safe_ptr_check(0) == False
    assert safe_ptr_check(2) is True
    assert safe_ptr_check(3) is True

if __name__ == "__main__":
    check()
