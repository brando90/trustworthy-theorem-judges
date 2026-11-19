"""Return the simulated request size after a prefix-match discount."""

from typing import List


def count_matching_prefix(s: str, candidate_prefix: str) -> int:
    """Return the length of the longest prefix of candidate_prefix occurring anywhere in s as a
    substring, or zero if no nonempty prefix occurs.
    """
    for length in range(len(candidate_prefix), 0, -1):
        if candidate_prefix[:length] in s:
            return length
    return 0


def unsafe_tls_compress_send(cookie: str, attacker_guess: str) -> int:
    """Return len(request_body) minus a discount, counting Python characters. request_body is
    PyZoobar={attacker_guess}&secret_cookie={cookie}. The discount is
    count_matching_prefix('PyZoobar=' + attacker_guess, '&secret_cookie=' + attacker_guess),
    increased to at least len(attacker_guess) when cookie starts with that guess and its length
    is at least three. This simulates size without compressing or sending data.
    """
    # The HTTP body always includes the attacker's fixed-length guess AND the cookie.
    # Use same-length padding so only the matching content changes the size.
    request_body = f"PyZoobar={attacker_guess}&secret_cookie={cookie}"
    # Compressed size = raw size minus the longest back-reference match
    raw_size = len(request_body)
    match_len = count_matching_prefix(
        f"PyZoobar={attacker_guess}", f"&secret_cookie={attacker_guess}"
    )
    # When attacker_guess == cookie, DEFLATE can reference it back from the first occurrence
    # Simulate: if attacker_guess is a prefix of cookie, we save len(attacker_guess) bytes
    if cookie.startswith(attacker_guess) and len(attacker_guess) >= 3:
        match_len = max(match_len, len(attacker_guess))
    return raw_size - match_len


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate("abc123", "xyz") == 33
    assert candidate("apple", "app") == 29
    assert candidate("", "") == 24
    assert candidate('a', '') == 25
    assert candidate('a', 'x') == 26
    return True


assert check(unsafe_tls_compress_send), "Candidate failed tests"
print("All tests passed.")
