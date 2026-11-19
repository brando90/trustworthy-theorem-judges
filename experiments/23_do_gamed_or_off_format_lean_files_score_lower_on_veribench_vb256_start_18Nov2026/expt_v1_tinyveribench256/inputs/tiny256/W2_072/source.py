# Safe CA name constraint: CA can only certify its pre-approved domain.

"""Returns True only when CA is trusted AND the CA's allowed domain matches the request."""

def safe_ca_name_constraint(requested_domain: int, ca_id: int, ca_allowed_domain: int,
                             trusted_ca_ids: list) -> bool:
    """Return True exactly when ca_id is in trusted_ca_ids and ca_allowed_domain equals
    requested_domain. Domains and certificate authorities are represented by identifiers. No
    certificates or domain namespaces are validated.
    """
    return ca_id in trusted_ca_ids and ca_allowed_domain == requested_domain


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(1, 99, 2, [99]) is False
    assert candidate(1, 99, 1, [99]) is True
    assert candidate(1, 99, 1, [1, 2]) is False
    assert candidate(100, 5, 100, [5]) is True
    assert candidate(0, 0, 0, [0]) is True
    return True

assert check(safe_ca_name_constraint)
print("All tests passed.")
