
"""Model host-key acceptance by requiring a nonempty presented fingerprint string equal to the
trusted fingerprint string. IP and hostname arguments are ignored. No cryptographic verification
is performed.
"""

def safe_rlogin_reverse_dns(
    client_ip: int,
    reverse_dns_hostname: str,
    trusted_hostname: str,
    presented_host_key_fingerprint: str,
    trusted_host_key_fingerprint: str,
) -> bool:
    """Return False for an empty presented fingerprint. Otherwise return whether the two supplied
    fingerprint strings are equal. Ignore client_ip and both hostname arguments. This comparison
    performs no cryptographic verification.
    """
    # Reverse DNS hostname is logging/display only — NOT used for authentication.
    _ = client_ip
    _ = reverse_dns_hostname
    _ = trusted_hostname

    # The ONLY authentication check: cryptographic host-key fingerprint match.
    if presented_host_key_fingerprint == "":
        return False  # No host key presented — reject.
    return presented_host_key_fingerprint == trusted_host_key_fingerprint


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(3232235777, 'trusted.example.com', 'trusted.example.com', 'SHA256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa', 'SHA256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa') == True
    assert candidate(195939070, 'trusted.example.com', 'trusted.example.com', 'SHA256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb', 'SHA256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa') == False
    assert candidate(3232235777, 'wrong.reverse.dns', 'trusted.example.com', 'SHA256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa', 'SHA256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa') == True
    assert candidate(3232235777, 'trusted.example.com', 'trusted.example.com', '', 'SHA256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa') == False
    assert candidate(195939070, 'trusted.example.com', 'trusted.example.com', '', 'SHA256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa') == False
    return True


if __name__ == "__main__":
    assert check(safe_rlogin_reverse_dns), f"Failed: {__file__}"
