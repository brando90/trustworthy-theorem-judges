"""Return a simulated authentication tag by adding msg to 31 times shared_key and reducing modulo
100003.
"""
from typing import Callable


def safe_deniable_auth(msg: int, shared_key: int) -> int:
    """Return a simulated authentication tag by adding msg to 31 times shared_key and reducing
    modulo 100003.
    """
    return (msg + 31 * shared_key) % 100003


def verify_safe(msg: int, tag: int, shared_key: int) -> bool:
    """Return whether tag equals (msg + 31 * shared_key) modulo 100003, using the supplied integers."""
    return tag == (msg + 31 * shared_key) % 100003


def third_party_verifiable(_msg: int, _shared_key: int) -> bool:
    """Return False regardless of either argument, representing a fixed simulated verification
    status.
    """
    return False


def bob_can_forge(msg: int, shared_key: int) -> int:
    """Return the modeled tag Bob can compute for msg from the supplied shared key."""
    return (msg + 31 * shared_key) % 100003


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert third_party_verifiable(42, 7) is False
    assert third_party_verifiable(999, 12345) is False
    assert candidate(0, 0) == 0
    assert candidate(1, 0) == 1
    assert candidate(1, 1) == 32
    return True


if __name__ == "__main__":
    assert check(safe_deniable_auth), f"Failed: {__file__}"
    print("All tests passed.")
