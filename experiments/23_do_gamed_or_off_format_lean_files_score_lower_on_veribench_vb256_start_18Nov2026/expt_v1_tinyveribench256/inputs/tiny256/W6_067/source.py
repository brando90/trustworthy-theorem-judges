# Unsafe Tor circuit hop count: accepts circuits with too few hops.

"""Return True without consulting how many hops the circuit has."""

def unsafe_circuit_hops(hop_count: int) -> bool:
    """Return True without consulting how many hops the circuit has."""
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_circuit_hops(3) == True
    assert unsafe_circuit_hops(1) == True
    assert unsafe_circuit_hops(0) == True
    assert unsafe_circuit_hops(2) is True
    assert unsafe_circuit_hops(7) is True

if __name__ == "__main__":
    check()
