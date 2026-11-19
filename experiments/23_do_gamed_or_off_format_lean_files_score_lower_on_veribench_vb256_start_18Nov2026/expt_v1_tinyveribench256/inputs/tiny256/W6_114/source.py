# Unsafe SYN handler: accepts new SYN connections without checking the half-open connection limit.

"""Returns True for every incoming SYN regardless of current half-open count."""

def unsafe_syn_flood(half_open_count: int, max_half_open: int) -> bool:
    """Returns True for every incoming SYN regardless of current half-open count."""
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_syn_flood(0, 128) == True
    assert unsafe_syn_flood(128, 128) == True
    assert unsafe_syn_flood(999, 128) == True
    assert unsafe_syn_flood(0, 0) is True
    assert unsafe_syn_flood(1, 1) is True

if __name__ == "__main__":
    check()
