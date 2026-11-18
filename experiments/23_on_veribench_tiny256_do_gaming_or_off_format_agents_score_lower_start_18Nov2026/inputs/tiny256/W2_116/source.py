# Safe DNS check: accepts responses only when query_id == response_id.

"""Returns True only when response_id exactly matches query_id."""

def safe_dns_check(query_id: int, response_id: int) -> bool:
    """Returns True only when response_id exactly matches query_id.

    MIT 6.858 Quiz 2, Fall 2013: Network / DNS spoofing.
    """
    return query_id == response_id


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_dns_check(42, 42) == True
    assert safe_dns_check(42, 99) == False
    assert safe_dns_check(0, 0) == True
    assert safe_dns_check(0, 1) == False
    assert safe_dns_check(1, 0) is False

if __name__ == "__main__":
    check()
