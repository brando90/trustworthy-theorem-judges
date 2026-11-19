# Unsafe DNS resolver: open to the world, no rate limit — DNS amplification DoS.

"""Toy DNS response model: ignore the spoofing flag, reject nonpositive query sizes, and otherwise
return a response flag with the integer response-to-query size ratio.
"""

def unsafe_dns_amplification(
    src_ip_spoofed: bool,
    query_size: int,
    response_size: int,
) -> tuple[bool, int]:
    """Return (False, 0) when query_size is nonpositive. Otherwise return (True, response_size //
    query_size). Ignore src_ip_spoofed. Sizes are integers, so negative response sizes can
    produce negative ratios. This function performs no network operations.
    """
    # Vulnerable: always respond, regardless of source or rate.
    _ = src_ip_spoofed  # intentionally ignored
    if query_size <= 0:
        return (False, 0)
    amplification = response_size // query_size
    return (True, amplification)


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(False, 64, 128) == (True, 2)
    assert candidate(True, 64, 3200) == (True, 50)
    assert candidate(True, 60, 6000) == (True, 100)
    assert candidate(False, 0, 128) == (False, 0)
    assert candidate(True, 128, 64) == (True, 0)
    return True


if __name__ == "__main__":
    assert check(unsafe_dns_amplification), f"Failed: {__file__}"
