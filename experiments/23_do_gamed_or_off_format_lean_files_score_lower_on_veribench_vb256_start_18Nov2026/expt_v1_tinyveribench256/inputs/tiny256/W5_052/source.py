# Unsafe function pointer overflow check: does not detect strcpy overwriting a function pointer.

"""Approve the request without checking whether the input overflows buf into the function pointer."""

def unsafe_func_ptr_overflow(buf_size: int, input_len: int, fp_offset: int) -> bool:
    """Approve the request without checking whether the input overflows buf into the function
    pointer.

    MIT 6.858 Fall 2012 Quiz 1: strcpy overflows path into function pointer in struct request.
    """
    return True  # vulnerable: overflow into function pointer never detected


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_func_ptr_overflow(240, 100, 0) == True
    assert unsafe_func_ptr_overflow(240, 241, 0) == True
    assert unsafe_func_ptr_overflow(240, 300, 0) == True
    assert unsafe_func_ptr_overflow(240, 240, 0) == True
    assert unsafe_func_ptr_overflow(0, 0, 0) is True

if __name__ == "__main__":
    check()
