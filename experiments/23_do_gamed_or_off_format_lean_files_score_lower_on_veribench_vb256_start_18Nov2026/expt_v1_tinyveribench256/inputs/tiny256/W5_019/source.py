# Unsafe file integrity: no hash/MAC on file content; server can modify without detection.

"""Approve the request without checking whether stored hash matches expected."""

def unsafe_read_file(stored: int, expected: int) -> bool:
    """Approve the request without checking whether stored hash matches expected.

    MIT 6.858 Lab 5: Secure File System.
    """
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_read_file(42, 42) == True
    assert unsafe_read_file(99, 42) == True
    assert unsafe_read_file(0, 12345) == True
    assert unsafe_read_file(0, 0) is True
    assert unsafe_read_file(1, 42) is True

if __name__ == "__main__":
    check()
