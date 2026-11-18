# Unsafe LLC partition: any process can access any cache set — cross-process timing side-channel.

"""Return whether cache_set is less than total_sets, ignoring process_id. Negative cache indices
and totals are not rejected separately.
"""

def unsafeLLCAccess(process_id: int, cache_set: int, total_sets: int) -> bool:
    """Return cache_set < total_sets, ignoring process_id. No nonnegative index or total check is
    performed.
    """
    return cache_set < total_sets


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafeLLCAccess(0, 5, 16) == True
    assert unsafeLLCAccess(1, 5, 16) == True
    assert unsafeLLCAccess(0, 15, 16) == True
    assert unsafeLLCAccess(0, 16, 16) == False
    assert unsafeLLCAccess(0, 5, 7) is True

if __name__ == "__main__":
    check()
