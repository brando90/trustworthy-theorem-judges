# Unsafe version rollback: no version number on version structures; server can replay old VS.

"""Approve the request without checking whether server version is stale."""

def unsafe_vs_check(client_ver: int, server_ver: int) -> bool:
    """Approve the request without checking whether server version is stale.

    MIT 6.858 Lab 5: Secure File System.
    """
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_vs_check(5, 5) == True
    assert unsafe_vs_check(5, 3) == True
    assert unsafe_vs_check(100, 1) == True
    assert unsafe_vs_check(0, 5) is True
    assert unsafe_vs_check(5, 1) is True

if __name__ == "__main__":
    check()
