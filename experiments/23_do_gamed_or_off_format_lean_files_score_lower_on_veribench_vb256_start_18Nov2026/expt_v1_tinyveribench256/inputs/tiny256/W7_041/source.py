"""Model an unchecked Binder permission decision by returning True for every input."""

def unsafe_binder_call(service_id: int, caller_uid: int, required_permission: int) -> bool:
    """Return True unconditionally as a modeled permission decision. All three arguments are
    ignored. No service is invoked and no permission or caller validation occurs.
    """
    # Direct dispatch — no permission check, no UID validation
    return True  # Vulnerability: always allows


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(100, 1000, 1) == True
    assert candidate(100, 9999, 1) == True
    assert candidate(100, 1000, 999) == True
    assert candidate(100, 0, 1) == True
    assert candidate(0, 0, 0) is True
    return True


if __name__ == "__main__":
    assert check(unsafe_binder_call), f"Failed: {__file__}"
