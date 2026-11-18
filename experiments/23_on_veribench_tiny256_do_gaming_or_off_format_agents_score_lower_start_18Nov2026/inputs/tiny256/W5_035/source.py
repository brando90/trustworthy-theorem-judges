# Unsafe XFI direct-jump check: does not verify that a module's call target is an approved entry point.

"""Approve the request without checking whether target_addr is an approved module entry point."""

def unsafe_xfi_jump(target_addr: int, module_start: int, module_end: int,
                    approved_entries: list) -> bool:
    """Approve the request without checking whether target_addr is an approved module entry point.

    MIT 6.858 Fall 2009 Quiz 1: XFI — module jumping directly to unlink() in libc.
    """
    return True  # vulnerable: target never validated against approved entries


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_xfi_jump(134512896, 134512640, 134516736, [134512896, 134513152]) == True
    assert unsafe_xfi_jump(3085959168, 134512640, 134516736, [134512896, 134513152]) == True
    assert unsafe_xfi_jump(3735928559, 134512640, 134516736, [134512896, 134513152]) == True
    assert unsafe_xfi_jump(0, 134512640, 134516736, [134512896, 134513152]) == True
    assert unsafe_xfi_jump(0, 0, 0, []) is True

if __name__ == "__main__":
    check()
