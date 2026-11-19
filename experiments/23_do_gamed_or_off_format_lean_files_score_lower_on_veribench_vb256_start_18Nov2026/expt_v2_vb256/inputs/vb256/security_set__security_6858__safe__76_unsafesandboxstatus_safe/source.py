# Safe sandbox status: validates status code is within expected range before accepting.

"""Returns True only when min_valid <= status_code <= max_valid."""

def safe_sandbox_status(status_code: int, min_valid: int, max_valid: int) -> bool:
    """Returns True only when min_valid <= status_code <= max_valid."""
    return min_valid <= status_code <= max_valid


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_sandbox_status(5, 0, 10) == True
    assert safe_sandbox_status(0, 0, 10) == True
    assert safe_sandbox_status(10, 0, 10) == True
    assert safe_sandbox_status(11, 0, 10) == False
    assert safe_sandbox_status(0, 5, 10) == False

if __name__ == "__main__":
    check()
