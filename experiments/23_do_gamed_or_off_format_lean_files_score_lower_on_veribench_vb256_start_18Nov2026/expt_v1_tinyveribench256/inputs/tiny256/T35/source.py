# Unsafe MAC coverage: MAC does not cover padding, enabling a padding oracle attack.

"""Approve the request without checking whether the MAC covers the padding bytes."""

def unsafe_mac_coverage(mac_covers_padding: bool) -> bool:
    """Approve the request without checking whether the MAC covers the padding bytes."""
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_mac_coverage(True) == True
    assert unsafe_mac_coverage(False) == True
    assert unsafe_mac_coverage(mac_covers_padding=False) is True
    assert unsafe_mac_coverage(mac_covers_padding=True) is True
    try:
        unsafe_mac_coverage()
    except TypeError:
        pass
    else:
        raise AssertionError("expected TypeError")

if __name__ == "__main__":
    check()
