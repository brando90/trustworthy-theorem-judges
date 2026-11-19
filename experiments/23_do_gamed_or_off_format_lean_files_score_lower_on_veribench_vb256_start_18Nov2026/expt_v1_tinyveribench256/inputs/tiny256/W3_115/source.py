# Safe TCP sequence number validation: requires exact sequence number match.

"""Returns True only when seq_num equals expected_seq."""

def safe_tcp_seq_check(seq_num: int, expected_seq: int) -> bool:
    """Returns True only when seq_num equals expected_seq."""
    return seq_num == expected_seq


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_tcp_seq_check(100, 100) == True
    assert safe_tcp_seq_check(999, 100) == False
    assert safe_tcp_seq_check(0, 1) == False
    assert safe_tcp_seq_check(0, 0) is True
    assert safe_tcp_seq_check(2, 1) is False

if __name__ == "__main__":
    check()
