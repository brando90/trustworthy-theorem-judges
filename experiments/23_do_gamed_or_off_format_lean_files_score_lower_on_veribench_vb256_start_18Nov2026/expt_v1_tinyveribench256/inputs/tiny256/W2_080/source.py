# Safe file integrity: compares stored hash against expected hash to detect tampering.

"""Returns True only when stored hash equals the expected hash."""

def safe_read_file(stored: int, expected: int) -> bool:
    """Return True when stored equals expected, otherwise False. These integers represent hash
    values in this toy check. No file is read and no hash is computed or authenticated.
    """
    return stored == expected


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_read_file(42, 42) == True
    assert safe_read_file(99, 42) == False
    assert safe_read_file(0, 12345) == False
    assert safe_read_file(0, 0) == True
    assert safe_read_file(0, 1) is False

if __name__ == "__main__":
    check()
