# Unsafe return-to-libc check: does not verify that return address points to legitimate code.

"""Approve the request without checking whether return_addr is within the code segment."""

def unsafe_rop_check(return_addr: int, text_start: int, text_end: int) -> bool:
    """Approve the request without checking whether return_addr is within the code segment.

    MIT 6.858 Fall 2009 Quiz 1: buffer overflow / return-to-libc ROP chains.
    """
    return True  # vulnerable: return address never validated


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_rop_check(134512640, 134512640, 134516736) == True
    assert unsafe_rop_check(3085500416, 134512640, 134516736) == True
    assert unsafe_rop_check(0, 134512640, 134516736) == True
    assert unsafe_rop_check(3735928559, 134512640, 134516736) == True
    assert unsafe_rop_check(0, 0, 0) is True

if __name__ == "__main__":
    check()
