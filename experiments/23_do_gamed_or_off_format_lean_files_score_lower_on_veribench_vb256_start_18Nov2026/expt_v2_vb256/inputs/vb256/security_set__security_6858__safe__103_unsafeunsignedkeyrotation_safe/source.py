"""Model key rotation using a supplied signature-status flag. Return the new key when the flag is
true, otherwise None. No signature verification occurs.
"""
from typing import Callable, Optional


def safe_rotate(_old_key: int, new_key: int, signed_by_old: bool) -> Optional[int]:
    """Return new_key when signed_by_old is true, otherwise None. Ignore _old_key. The supplied
    flag represents signature status without cryptographic verification.
    """
    return new_key if signed_by_old else None


def rotation_accepted(old_key: int, new_key: int, signed: bool) -> bool:
    """Return whether safe_rotate returns a non-None key. For integer keys, this follows the
    supplied signed flag. Old_key is ignored and no signature is verified.
    """
    return safe_rotate(old_key, new_key, signed) is not None


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(100, 200, True) == 200
    assert candidate(100, 200, False) is None
    assert candidate(0, 0, True) == 0
    assert rotation_accepted(1, 2, True) is True
    assert rotation_accepted(1, 999, False) is False
    return True


if __name__ == "__main__":
    assert check(safe_rotate), f"Failed: {__file__}"
    print("All tests passed.")
