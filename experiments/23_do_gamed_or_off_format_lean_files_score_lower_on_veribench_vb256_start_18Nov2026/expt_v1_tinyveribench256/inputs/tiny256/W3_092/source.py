# Safe onion-routed forwarding — MIT 6.858 Lecture 19: Anonymous Communication (Tor)
# Each relay only learns its predecessor and successor — source stays hidden.

"""Toy route result: return the last relay and msg, or src_ip and msg for an empty route. dst_ip is
unused. No network forwarding, encryption, or relay knowledge is modeled.
"""

from typing import Optional


def safe_onion_route(src_ip: int, dst_ip: int, msg: int, relays: list[int]) -> tuple[int, int]:
    """Return the last relay and the supplied message. For an empty route, use the source IP in
    place of the relay.
    """
    if not relays:
        # No relays: direct connection as fallback (not anonymous, but valid)
        return (src_ip, msg)
    # Simulate forwarding: each relay only forwards (next_hop, msg)
    # The destination receives (relays[-1], msg) — src_ip is NOT present
    return (relays[-1], msg)


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    last_relay, msg = candidate(192168001, 8080, 42, [10, 20, 30])
    assert last_relay == 30
    assert msg == 42
    _, m = candidate(1, 2, 5, [])
    assert m == 5
    assert candidate(0, 0, 0, []) == (0, 0)
    assert candidate(1, 2, 5, [0]) == (0, 5)
    return True


assert check(safe_onion_route)
print("All tests passed.")
