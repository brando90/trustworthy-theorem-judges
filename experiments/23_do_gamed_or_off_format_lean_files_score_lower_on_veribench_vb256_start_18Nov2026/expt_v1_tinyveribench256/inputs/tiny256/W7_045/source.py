# Unsafe BGP route acceptance: any AS can announce any prefix (no authorization check).

"""Accept a BGP route announcement unconditionally."""

def unsafe_bgp_hijacking(announcing_as: int, prefix_owner_as: int, prefix: str) -> bool:
    """Accept a BGP route announcement unconditionally.

    Args:
        announcing_as: AS number that issued the announcement.
        prefix_owner_as: AS number that actually owns the prefix (ignored).
        prefix: IP prefix being announced (ignored).

    Returns:
        True, always — every announcement is accepted.
    """
    _ = (announcing_as, prefix_owner_as, prefix)
    return True  # No origin validation — every announcement accepted


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(64500, 64500, '192.0.2.0/24') is True
    assert candidate(64501, 64500, '192.0.2.0/24') is True
    assert candidate(64502, 64500, '192.0.2.0/25') is True
    assert candidate(1, 65000, '198.51.100.0/24') is True
    assert candidate(0, 0, '0.0.0.0/0') is True
    return True


if __name__ == "__main__":
    assert check(unsafe_bgp_hijacking)
    print("All tests passed.")
