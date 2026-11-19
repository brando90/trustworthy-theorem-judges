# Unsafe version install: accepts any signed OS image including older versions.

"""Approve the request without checking whether install_ver is newer than current_ver."""

def unsafe_version_install(current_ver: int, install_ver: int) -> bool:
    """Approve the request without checking whether install_ver is newer than current_ver."""
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_version_install(10, 11) == True
    assert unsafe_version_install(10, 10) == True
    assert unsafe_version_install(10, 9) == True
    assert unsafe_version_install(100, 1) == True
    assert unsafe_version_install(0, 0) == True

if __name__ == "__main__":
    check()
