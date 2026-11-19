# Safe DNS response handling: DNSSEC signature verification over (ip, trusted_key).

"""Simulate response acceptance using transaction-ID equality and an arithmetic signature word.
Return (True, response_ip) when both checks pass, otherwise (False, 0). The domain is ignored.
This is not cryptographic DNSSEC verification.
"""

def _compute_dnssec_signature(response_ip: int, trusted_key: int) -> int:
    """Return the simulated DNS signature word from response_ip plus 37 times trusted_key, reduced
    modulo 2**32.
    """
    return (response_ip + trusted_key * 37) % (2 ** 32)


def safe_dns_spoofing(query_domain: str, response_ip: int,
                      response_txid: int, expected_txid: int,
                      dnssec_signature: int, trusted_key: int) -> tuple:
    """Return (True, response_ip) when response_txid equals expected_txid and dnssec_signature
    equals (response_ip + 37 * trusted_key) modulo 2**32. Otherwise return (False, 0). Ignore
    query_domain. This toy arithmetic check does not verify DNSSEC cryptographically or update a
    cache.
    """
    if response_txid != expected_txid:
        return (False, 0)
    expected_sig = _compute_dnssec_signature(response_ip, trusted_key)
    if dnssec_signature == expected_sig:
        return (True, response_ip)
    return (False, 0)


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate('bank.com', 3735928559, 4660, 4660, 2576980377, 1111638594) == (False, 0)
    assert candidate('', 0, 0, 0, 0, 1111638594) == (False, 0)
    assert candidate('example.org', 42, 17, 17, 79, 1) == (True, 42)
    assert candidate('', 0, 0, 0, 0, 0) == (True, 0)
    assert candidate('e', 1, 1, 1, 1, 1) == (False, 0)
    return True


if __name__ == "__main__":
    assert check(safe_dns_spoofing)
    print("All tests passed.")
