# Safe return address check: validates that return address lies within the expected code segment.

"""Returns True only when return_addr is within [text_start, text_end)."""

def safe_rop_check(return_addr: int, text_start: int, text_end: int) -> bool:
    """Return True when text_start <= return_addr < text_end, otherwise False. Empty or reversed
    intervals return False. This checks supplied integer bounds without verifying code ownership
    or preventing return-oriented programming attacks.
    """
    return text_start <= return_addr < text_end


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_rop_check(134512640, 134512640, 134516736) == True
    assert safe_rop_check(134513920, 134512640, 134516736) == True
    assert safe_rop_check(3085500416, 134512640, 134516736) == False
    assert safe_rop_check(0, 134512640, 134516736) == False
    assert safe_rop_check(134516736, 134512640, 134516736) == False

if __name__ == "__main__":
    check()
