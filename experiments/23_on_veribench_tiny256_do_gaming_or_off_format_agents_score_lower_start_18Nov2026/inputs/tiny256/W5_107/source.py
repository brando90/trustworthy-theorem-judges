"""Look up a dictionary entry while ignoring the service token, returning None for a missing key.
Loading this module runs the fixed checks and prints a success message if they pass.
"""


def unsafe_service_auth(token: int, query_id: int,
                        db: dict[int, str]) -> str | None:
    """Return the value stored under query_id in db, or None if the key is absent. The token
    argument is ignored. No authorization check is performed.
    """
    return db.get(query_id)


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(100, 1, {1: 'alice@example.com', 2: 'secret_password_hash', 3: 'user_profile'}) == 'alice@example.com'
    assert candidate(100, 2, {1: 'alice@example.com', 2: 'secret_password_hash', 3: 'user_profile'}) == 'secret_password_hash'
    assert candidate(999, 3, {1: 'alice@example.com', 2: 'secret_password_hash', 3: 'user_profile'}) == 'user_profile'
    assert candidate(0, 1, {1: 'alice@example.com', 2: 'secret_password_hash', 3: 'user_profile'}) == 'alice@example.com'
    assert candidate(100, 1, {}) is None
    return True


assert check(unsafe_service_auth), "Candidate failed service auth tests"
print("All tests passed.")
