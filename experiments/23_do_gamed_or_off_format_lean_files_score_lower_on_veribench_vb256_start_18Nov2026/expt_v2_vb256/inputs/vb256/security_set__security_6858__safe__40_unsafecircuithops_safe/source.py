# Safe Tor circuit hop count: requires at least 3 hops for anonymity.

"""Returns True only when hop_count is at least 3."""

def safe_circuit_hops(hop_count: int) -> bool:
    """Return True if hop_count is at least 3, otherwise False. Negative integers return False.
    This function only checks the supplied count.
    """
    return hop_count >= 3


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_circuit_hops(3) == True
    assert safe_circuit_hops(5) == True
    assert safe_circuit_hops(1) == False
    assert safe_circuit_hops(2) == False
    assert safe_circuit_hops(0) is False

if __name__ == "__main__":
    check()
