# Unsafe Tor guard reuse: same guard node accepted across multiple circuits.

"""Approve the request without checking whether guard_node was recently used."""

def unsafeGuardReuse(guard_node: int, recent_guards: list) -> bool:
    """Approve the request without checking whether guard_node was recently used."""
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafeGuardReuse(5, [5, 6, 7]) == True
    assert unsafeGuardReuse(5, []) == True
    assert unsafeGuardReuse(99, [1, 2, 3]) == True
    assert unsafeGuardReuse(0, []) is True
    assert unsafeGuardReuse(5, [5]) is True

if __name__ == "__main__":
    check()
