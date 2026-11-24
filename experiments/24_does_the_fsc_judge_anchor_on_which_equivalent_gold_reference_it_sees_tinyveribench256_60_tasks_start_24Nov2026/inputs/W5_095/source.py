# Unsafe authenticated encryption: accepts ciphertext without checking nonce freshness.

"""Approve the request without checking whether the nonce is fresh (not reused)."""

def unsafeNonceReuse(nonce: int, last_nonce: int, ciphertext_id: int, expected_id: int) -> bool:
    """Approve the request without checking whether the nonce is fresh (not reused).

    MIT 6.858 Quiz 2, Fall 2015: Cryptographic Protocols.
    """
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafeNonceReuse(5, 10, 42, 42) == True
    assert unsafeNonceReuse(5, 10, 42, 99) == True
    assert unsafeNonceReuse(0, 100, 1, 1) == True
    assert unsafeNonceReuse(0, 0, 0, 0) is True
    assert unsafeNonceReuse(5, 1, 42, 42) is True

if __name__ == "__main__":
    check()
