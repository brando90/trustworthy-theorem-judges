"""Return whether attempts < max_attempts and stored_key == entered_key. Attempt counts are
supplied by the caller and are not updated. Teaching model for MIT 6.858.
"""

from typing import Callable


def safe_passcode_check(
    stored_key: int,
    entered_key: int,
    attempts: int,
    max_attempts: int,
) -> bool:
    """Return True exactly when attempts < max_attempts and stored_key == entered_key. Otherwise
    return False. Integer arguments, including negative attempt counts, are compared directly.
    The function does not increment attempts or maintain lockout state.
    """
    if attempts >= max_attempts:
        return False   # locked out
    return stored_key == entered_key


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(1234, 1234, 0, 10) is True
    assert candidate(1234, 1234, 9, 10) is True
    assert candidate(1234, 1234, 0, 0) is False
    assert candidate(1234, 9999, 0, 10) is False
    assert candidate(1234, 1234, 10, 10) is False
    return True


if __name__ == "__main__":
    assert check(safe_passcode_check), f"Failed: {__file__}"
    print("All tests passed.")
