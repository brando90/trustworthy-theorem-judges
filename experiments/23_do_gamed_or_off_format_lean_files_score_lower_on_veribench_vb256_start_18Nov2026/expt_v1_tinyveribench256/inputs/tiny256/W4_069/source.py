# Safe DNS reply validation: requires both query ID and source port to match — prevents Kaminsky attack.

"""Model a DNS reply acceptance predicate: return True exactly when the supplied query identifier
and source port match their expected values.
"""

def safe_dns_reply(query_id: int, expected_id: int, src_port: int, expected_port: int) -> bool:
    """Return whether both the query identifier and source port match the expected values."""
    return query_id == expected_id and src_port == expected_port


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_dns_reply(42, 42, 1, 1) == True
    assert safe_dns_reply(42, 42, 999, 1) == False
    assert safe_dns_reply(1, 2, 1, 1) == False
    assert safe_dns_reply(0, 0, 0, 0) == True
    assert safe_dns_reply(0, 2, 1, 1) is False

if __name__ == "__main__":
    check()
