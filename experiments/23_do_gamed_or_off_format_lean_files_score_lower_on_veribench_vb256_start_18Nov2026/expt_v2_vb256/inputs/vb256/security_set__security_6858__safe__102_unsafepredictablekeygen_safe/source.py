"""Return a modeled 32-bit key by multiplying session_id by 1000000007, adding the caller-supplied
fresh_nonce and reducing modulo 2**32.

Teaching model for MIT 6.858.
"""


def safe_key_gen(session_id: int, fresh_nonce: int) -> int:
    """Return a modeled 32-bit key by multiplying session_id by 1000000007, adding the
    caller-supplied fresh_nonce and reducing modulo 2**32.
    """
    return (session_id * 1000000007 + fresh_nonce) % (2**32)


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(1, 100) == 1000000107
    assert candidate(3, 12) == 3000000033
    assert candidate(0, 0) == 0
    assert candidate(0, 1) == 1
    assert candidate(2, 2) == 2000000016
    return True


assert check(safe_key_gen), "Candidate failed tests"
print("All tests passed.")
