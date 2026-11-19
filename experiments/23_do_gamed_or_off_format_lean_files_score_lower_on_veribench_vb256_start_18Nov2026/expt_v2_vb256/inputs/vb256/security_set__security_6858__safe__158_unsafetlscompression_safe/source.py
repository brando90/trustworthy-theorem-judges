"""Return the character count of a constructed request-body string containing the guess and cookie.
No compression, encryption, or transmission is performed.
"""

from typing import Callable


def safe_tls_send(cookie: str, attacker_guess: str) -> int:
    """Return len of the string formed by concatenating 'PyZoobar=', attacker_guess,
    '&secret_cookie=', and cookie: 24 plus both input character counts. No compression,
    encryption, or transmission is performed.
    """
    # No compression: attacker_guess and cookie are always fully transmitted
    request_body = f"PyZoobar={attacker_guess}&secret_cookie={cookie}"
    return len(request_body)


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate("abc123", "xyz") == 33
    assert candidate("apple", "app") == 32
    assert candidate("", "") == 24
    assert candidate('a', '') == 25
    assert candidate('a', 'x') == 26
    return True


if __name__ == "__main__":
    assert check(safe_tls_send), f"Failed: {__file__}"
    print("All tests passed.")
