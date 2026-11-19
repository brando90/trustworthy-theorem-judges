# Safe SYN handler: accepts new SYN only when the half-open connection count is below the limit.

"""Returns True only when half_open_count < max_half_open."""

def safe_syn_flood(half_open_count: int, max_half_open: int) -> bool:
    """Return whether half_open_count is strictly less than max_half_open. Equal counts return
    False. This comparison does not update connection counts or manage server resources.
    """
    return half_open_count < max_half_open


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_syn_flood(0, 128) == True
    assert safe_syn_flood(127, 128) == True
    assert safe_syn_flood(128, 128) == False
    assert safe_syn_flood(999, 128) == False
    assert safe_syn_flood(0, 1) is True

if __name__ == "__main__":
    check()
