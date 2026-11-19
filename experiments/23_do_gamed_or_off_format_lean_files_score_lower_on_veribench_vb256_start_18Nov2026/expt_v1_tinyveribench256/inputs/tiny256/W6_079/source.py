# Unsafe TCP sequence number validation: always accepts any sequence number.

"""Approve the request without checking whether seq_num matches expected_seq."""

def unsafe_tcp_seq_check(seq_num: int, expected_seq: int) -> bool:
    """Approve the request without checking whether seq_num matches expected_seq."""
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_tcp_seq_check(100, 100) == True
    assert unsafe_tcp_seq_check(999, 100) == True
    assert unsafe_tcp_seq_check(0, 9999) == True
    assert unsafe_tcp_seq_check(0, 0) is True
    assert unsafe_tcp_seq_check(1, 100) is True

if __name__ == "__main__":
    check()
