"""Encode the session key and two participant IDs as session_key + 100*alice + 10000*bob.

Teaching model for MIT 6.858.
"""
from typing import Callable


def safe_handshake_msg(session_key: int, alice: int, bob: int) -> int:
    """Encode the session key and two participant IDs as session_key + 100*alice + 10000*bob."""
    return session_key + 100 * alice + 10000 * bob


def safe_accept(msg: int, expected_key: int, expected_alice: int, expected_bob: int) -> bool:
    """True iff msg equals the handshake payload for the expected key, alice and bob."""
    return msg == safe_handshake_msg(expected_key, expected_alice, expected_bob)


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(2, 2, 2) == 20202
    assert candidate(3, 3, 3) == 30303
    assert candidate(0, 0, 0) == 0
    assert candidate(1, 0, 0) == 1
    assert candidate(2, 1, 2) == 20102
    return True


if __name__ == "__main__":
    assert check(safe_handshake_msg), f"Failed: {__file__}"
    print("All tests passed.")
