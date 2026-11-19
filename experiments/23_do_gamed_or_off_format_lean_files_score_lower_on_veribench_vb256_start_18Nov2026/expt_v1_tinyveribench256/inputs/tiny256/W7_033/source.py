
"""Model unconditional content acceptance by returning True regardless of inputHasScript. No
content is inspected, sanitized, or rendered.
"""

def unsafeXSSEcho(inputHasScript: bool) -> bool:
    """Return True regardless of inputHasScript, representing unconditional acceptance. No content
    is inspected, sanitized, or rendered.
    """
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafeXSSEcho(False) == True
    assert unsafeXSSEcho(True) == True
    assert unsafeXSSEcho(inputHasScript=False) is True
    assert unsafeXSSEcho(inputHasScript=True) is True
    try:
        unsafeXSSEcho()
    except TypeError:
        pass
    else:
        raise AssertionError("expected TypeError")

if __name__ == "__main__":
    check()
