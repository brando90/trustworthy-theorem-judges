"""Return the supplied server key when the caller-supplied external-proof validity flag is True,
otherwise None. No identity proofs are checked here.
"""
from typing import Callable, Optional


def safe_bare_lookup(server_key: int, external_proofs_valid: bool) -> Optional[int]:
    """Return server_key when external_proofs_valid is True, otherwise None. The caller supplies
    this validity flag. The function does not verify identity proofs.
    """
    return server_key if external_proofs_valid else None


def client_accepts(server_key: int, proofs_valid: bool) -> bool:
    """Return whether safe_bare_lookup returns a non-None key. For integer server_key inputs, this
    is True exactly when the caller-supplied proofs_valid flag is True. No identity proofs are
    verified.
    """
    return safe_bare_lookup(server_key, proofs_valid) is not None


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(1234, True) == 1234
    assert candidate(1234, False) is None
    assert candidate(0, True) == 0
    assert client_accepts(100, True) is True
    assert client_accepts(9999, False) is False
    return True


if __name__ == "__main__":
    assert check(safe_bare_lookup), f"Failed: {__file__}"
    print("All tests passed.")
