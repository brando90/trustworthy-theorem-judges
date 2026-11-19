# Unsafe out-of-band authentication: accepts messages without OOB verification.

"""Approve the request without checking whether out-of-band verification was performed."""

def unsafe_oob_auth(msg_id: int, has_oob_verification: bool) -> bool:
    """Approve the request without checking whether out-of-band verification was performed."""
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_oob_auth(1, True) == True
    assert unsafe_oob_auth(1, False) == True
    assert unsafe_oob_auth(99, False) == True
    assert unsafe_oob_auth(0, True) is True
    assert unsafe_oob_auth(99, True) is True

if __name__ == "__main__":
    check()
