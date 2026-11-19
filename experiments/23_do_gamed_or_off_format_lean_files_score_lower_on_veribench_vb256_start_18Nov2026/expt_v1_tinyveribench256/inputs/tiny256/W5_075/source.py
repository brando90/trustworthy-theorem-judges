# Unsafe DNS spoofing check: accepts responses without validating the query ID.

"""Approve the request without checking whether response_id matches query_id."""

def unsafe_dns_check(query_id: int, response_id: int) -> bool:
    """Approve the request without checking whether response_id matches query_id.

    MIT 6.858 Quiz 2, Fall 2013: Network / DNS spoofing.
    """
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_dns_check(42, 42) == True
    assert unsafe_dns_check(42, 99) == True
    assert unsafe_dns_check(0, 1) == True
    assert unsafe_dns_check(0, 0) is True
    assert unsafe_dns_check(2, 1) is True

if __name__ == "__main__":
    check()
