# Unsafe heap write: always permits writes regardless of chunk size, enabling heap buffer overflow exploits.

"""Approve the request without checking whether write_size exceeds chunk_size."""

def unsafe_heap_write(chunk_size: int, write_size: int) -> bool:
    """Approve the request without checking whether write_size exceeds chunk_size."""
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_heap_write(64, 32) == True
    assert unsafe_heap_write(64, 128) == True
    assert unsafe_heap_write(0, 1) == True
    assert unsafe_heap_write(0, 0) is True
    assert unsafe_heap_write(2, 1) is True

if __name__ == "__main__":
    check()
