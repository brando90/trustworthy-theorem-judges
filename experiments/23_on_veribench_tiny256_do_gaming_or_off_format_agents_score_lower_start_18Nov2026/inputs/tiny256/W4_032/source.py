
"""Model descriptor permission by membership in an allowlist. No file descriptors are closed,
inherited, or otherwise modified.
"""

def safe_fd_inherit(fd: int, allowed_fds: list) -> bool:
    """Return whether fd is in allowed_fds. This membership check does not close descriptors or
    configure child-process inheritance.
    """
    return fd in allowed_fds


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_fd_inherit(3, [3, 4]) == True
    assert safe_fd_inherit(4, [3, 4]) == True
    assert safe_fd_inherit(5, [3, 4]) == False
    assert safe_fd_inherit(3, []) is False
    assert safe_fd_inherit(3, [3]) is True

if __name__ == "__main__":
    check()
