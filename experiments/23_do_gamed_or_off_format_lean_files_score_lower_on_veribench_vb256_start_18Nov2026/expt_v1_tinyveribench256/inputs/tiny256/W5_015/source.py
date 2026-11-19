# Unsafe CA scope: any trusted CA can issue a certificate for any domain.

"""Returns True if the CA is trusted, regardless of the requested domain."""

def unsafe_any_root_ca_scope(requested_domain: int, ca_id: int, trusted_ca_ids: list) -> bool:
    """Returns True if the CA is trusted, regardless of the requested domain."""
    return ca_id in trusted_ca_ids  # any trusted CA can certify any domain


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(1, 99, [99]) is True
    assert candidate(1, 99, [1, 2]) is False
    assert candidate(1, 5, [5]) is True
    assert candidate(999, 5, [5]) is True
    assert candidate(0, 0, []) is False
    return True

assert check(unsafe_any_root_ca_scope)
print("All tests passed.")
