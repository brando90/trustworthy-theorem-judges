# Safe ARP response handling: verifies the response IP matches the requested IP.

"""Returns True only when the ARP response IP matches the expected IP."""

def safe_arp_response(response_ip: int, expected_ip: int) -> bool:
    """Return True when response_ip equals expected_ip, and False otherwise. This integer
    comparison does not authenticate the sender or prevent ARP cache poisoning.
    """
    return response_ip == expected_ip


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_arp_response(10, 10) == True
    assert safe_arp_response(99, 10) == False
    assert safe_arp_response(0, 1) == False
    assert safe_arp_response(0, 0) is True
    assert safe_arp_response(2, 1) is False

if __name__ == "__main__":
    check()
