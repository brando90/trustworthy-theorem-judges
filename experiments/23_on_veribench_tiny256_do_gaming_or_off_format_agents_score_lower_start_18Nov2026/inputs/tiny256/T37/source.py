# Unsafe key server acceptance: uses any key returned by the server without verification.

"""Approve the request without checking whether server_key matches expected_key."""

def unsafe_key_server_accept(server_key: int, expected_key: int) -> bool:
    """Approve the request without checking whether server_key matches expected_key."""
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_key_server_accept(42, 42) == True
    assert unsafe_key_server_accept(99, 42) == True
    assert unsafe_key_server_accept(0, 42) == True
    assert unsafe_key_server_accept(0, 0) is True
    assert unsafe_key_server_accept(1, 42) is True

if __name__ == "__main__":
    check()
