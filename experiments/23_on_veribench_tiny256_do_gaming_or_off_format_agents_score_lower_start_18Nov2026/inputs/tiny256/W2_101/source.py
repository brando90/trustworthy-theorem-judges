# Safe function pointer overflow check: rejects inputs that would overflow buf into the function pointer.

"""Provide a toy length guard returning whether input_len is strictly less than buf_size. Equality
is rejected, negative integers are compared without validation, and fp_offset is ignored.
"""

def safe_func_ptr_overflow(buf_size: int, input_len: int, fp_offset: int) -> bool:
    """Return input_len < buf_size, reserving one position for a modeled null terminator. Equality
    returns False. Negative lengths and sizes are compared without validation. fp_offset is
    ignored. No buffer access or copying occurs.
    """
    return input_len < buf_size  # strict less-than: room for null terminator


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_func_ptr_overflow(240, 100, 0) == True
    assert safe_func_ptr_overflow(240, 239, 0) == True
    assert safe_func_ptr_overflow(240, 240, 0) == False
    assert safe_func_ptr_overflow(240, 241, 0) == False
    assert safe_func_ptr_overflow(240, 300, 0) == False

if __name__ == "__main__":
    check()
