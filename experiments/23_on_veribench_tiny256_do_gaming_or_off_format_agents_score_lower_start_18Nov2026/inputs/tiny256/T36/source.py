# Unsafe null pointer dereference check: accepts null pointers without validation.

"""Approve the request without checking whether ptr_val is null (0)."""

def unsafe_ptr_check(ptr_val: int) -> bool:
    """Approve the request without checking whether ptr_val is null (0).

    MIT 6.858 Spring 2013 Quiz 1: memory safety / null pointer dereference.
    """
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_ptr_check(1) == True
    assert unsafe_ptr_check(0) == True
    assert unsafe_ptr_check(3735928559) == True
    assert unsafe_ptr_check(2) is True
    assert unsafe_ptr_check(3) is True

if __name__ == "__main__":
    check()
