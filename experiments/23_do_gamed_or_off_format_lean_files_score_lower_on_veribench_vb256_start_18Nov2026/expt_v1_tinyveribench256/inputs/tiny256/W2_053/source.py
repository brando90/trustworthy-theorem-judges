# Safe DHCP client: enforces DHCP snooping (trusted server whitelist).

"""Model DHCP offer acceptance by comparing supplied server identifiers. A matching nonzero
authorized identifier permits returning the offered configuration. No server authentication
occurs.
"""

def safe_dhcp_spoofing(
    offer_server_ip: int,
    offer_client_ip: int,
    offer_gateway_ip: int,
    offer_dns_ip: int,
    authorized_server_ip: int,
) -> tuple[bool, int, int, int]:
    """Return (False, 0, 0, 0) when authorized_server_ip is zero or differs from offer_server_ip.
    Otherwise return (True, offer_client_ip, offer_gateway_ip, offer_dns_ip). Compare supplied
    integers only. Do not authenticate the server or validate the offered addresses.
    """
    # Required: authorized server must be configured (non-zero).
    if authorized_server_ip == 0:
        return (False, 0, 0, 0)
    # Required: OFFER source must be the authorized server.
    if offer_server_ip != authorized_server_ip:
        return (False, 0, 0, 0)
    return (True, offer_client_ip, offer_gateway_ip, offer_dns_ip)


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(3232235777, 3232235786, 3232235777, 134744072, 3232235777) == (True, 3232235786, 3232235777, 134744072)
    assert candidate(3232235929, 3232235786, 3232235929, 3232235929, 3232235777) == (False, 0, 0, 0)
    assert candidate(3232235777, 3232235786, 3232235777, 134744072, 0) == (False, 0, 0, 0)
    assert candidate(0, 3232235786, 3232235777, 134744072, 3232235777) == (False, 0, 0, 0)
    assert candidate(3232235777, 3232235787, 3232235777, 134744072, 3232235777) == (True, 3232235787, 3232235777, 134744072)
    return True


if __name__ == "__main__":
    assert check(safe_dhcp_spoofing), f"Failed: {__file__}"
