# Unsafe DB proxy: executes any service query without a whitelist check, enabling cross-service data access.

"""Approve the request without checking whether (service_id, query_type) is in whitelist."""

def unsafe_query_check(service_id: int, query_type: int, whitelist: list) -> bool:
    """Approve the request without checking whether (service_id, query_type) is in whitelist."""
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_query_check(1, 10, [(1, 10), (2, 20)]) == True
    assert unsafe_query_check(3, 99, [(1, 10), (2, 20)]) == True
    assert unsafe_query_check(0, 0, []) == True
    assert unsafe_query_check(1, 0, []) is True
    assert unsafe_query_check(1, 1, [(1, 10)]) is True

if __name__ == "__main__":
    check()
