"""Look up a stored query result when the supplied token's permission list contains the query
identifier. Return None when permission or the stored result is absent.
"""

from typing import Callable


def safe_service_auth(token: int, query_id: int,
                      allowed: dict[int, list[int]],
                      db: dict[int, str]) -> str | None:
    """Return db.get(query_id) if token is present in allowed and query_id belongs to
    allowed[token]. Otherwise return None. An authorized query missing from db also returns
    None. Tokens are supplied integer keys. No query execution or token secrecy is implemented.
    """
    if token not in allowed:
        return None
    if query_id not in allowed[token]:
        return None
    return db.get(query_id)


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(100, 1, {100: [1, 3], 200: [2]}, {1: 'alice@example.com', 2: 'secret_password_hash', 3: 'user_profile'}) == 'alice@example.com'
    assert candidate(100, 3, {100: [1, 3], 200: [2]}, {1: 'alice@example.com', 2: 'secret_password_hash', 3: 'user_profile'}) == 'user_profile'
    assert candidate(100, 2, {100: [1, 3], 200: [2]}, {1: 'alice@example.com', 2: 'secret_password_hash', 3: 'user_profile'}) is None
    assert candidate(0, 1, {100: [1, 3], 200: [2]}, {1: 'alice@example.com', 2: 'secret_password_hash', 3: 'user_profile'}) is None
    assert candidate(200, 2, {100: [1, 3], 200: [2]}, {1: 'alice@example.com', 2: 'secret_password_hash', 3: 'user_profile'}) == 'secret_password_hash'
    return True


if __name__ == "__main__":
    assert check(safe_service_auth), f"Failed: {__file__}"
    print("All tests passed.")
