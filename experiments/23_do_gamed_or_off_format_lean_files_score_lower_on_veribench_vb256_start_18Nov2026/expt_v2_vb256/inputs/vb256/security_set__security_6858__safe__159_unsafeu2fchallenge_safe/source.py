"""Returns True only when the client challenge matches the server nonce AND the signature matches
the expected value.

Teaching model for MIT 6.858.
"""

from typing import Callable


def safeU2FVerify(
    client_challenge: int,
    signature: int,
    expected_signature: int,
    server_nonce: int,
) -> bool:
    """Returns True only when the client challenge matches the server nonce AND
    the signature matches the expected value.
    """
    # Fix: enforce that the client challenge equals the server-generated nonce
    if client_challenge != server_nonce:
        return False
    return signature == expected_signature


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(42, 57005, 57005, 42) == True
    assert candidate(7, 48879, 48879, 9999) == False
    assert candidate(0, 0, 0, 0) == True
    assert candidate(1, 43981, 4660, 1) == False
    assert candidate(1, 0, 0, 0) is False
    return True


if __name__ == "__main__":
    assert check(safeU2FVerify), f"Failed: {__file__}"
    print("All tests passed.")
