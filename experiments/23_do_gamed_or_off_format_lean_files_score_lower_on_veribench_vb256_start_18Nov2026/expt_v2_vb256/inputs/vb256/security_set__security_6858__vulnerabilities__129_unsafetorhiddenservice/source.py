# Unsafe Tor hidden-service rendezvous: does not authenticate the rendezvous point.

"""Approve the request without checking whether the rendezvous point is controlled by an adversary."""

def unsafe_tor_rendezvous(rendezvous_addr: int, is_malicious: bool, hidden_service_connects: bool) -> bool:
    """Approve the request without checking whether the rendezvous point is controlled by an
    adversary.

    MIT 6.858 Fall 2012 Quiz 2: Tor hidden service deanonymized via malicious rendezvous point.
    """
    return True  # vulnerable: rendezvous never authenticated


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_tor_rendezvous(167772161, False, True) == True
    assert unsafe_tor_rendezvous(3735928559, True, True) == True
    assert unsafe_tor_rendezvous(0, True, False) == True
    assert unsafe_tor_rendezvous(2130706433, False, False) == True
    assert unsafe_tor_rendezvous(0, True, True) is True

if __name__ == "__main__":
    check()
