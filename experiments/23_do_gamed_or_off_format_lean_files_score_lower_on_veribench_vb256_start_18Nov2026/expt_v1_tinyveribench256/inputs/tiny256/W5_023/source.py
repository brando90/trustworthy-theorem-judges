# Unsafe plaintext file system: files stored without encryption; server reads plaintext.

"""Approve the request without checking whether server knows the file key."""

def unsafe_file_access(file_key: int, server_key: int) -> bool:
    """Approve the request without checking whether server knows the file key.

    MIT 6.858 Lab 5: Secure File System.
    """
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_file_access(100, 100) == True
    assert unsafe_file_access(100, 999) == True
    assert unsafe_file_access(42, 0) == True
    assert unsafe_file_access(0, 0) is True
    assert unsafe_file_access(42, 1) is True

if __name__ == "__main__":
    check()
