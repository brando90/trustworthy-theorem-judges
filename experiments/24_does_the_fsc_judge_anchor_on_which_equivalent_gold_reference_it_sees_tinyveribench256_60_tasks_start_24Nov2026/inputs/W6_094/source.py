"""Look up user_id directly in the database and return its value or None. The supplied service
credentials do not restrict this lookup.

Teaching model for MIT 6.858.
"""


def unsafe_per_user_ticket(service_token: int, user_id: int,
                            ticket: int, db: dict[int, str]) -> str | None:
    """Look up user_id directly in the database and return its value or None. The supplied service
    credentials do not restrict this lookup.
    """
    return db.get(user_id)  # ticket never checked — vulnerability


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(100, 1, 999, {1: 'alice_profile', 2: 'bob_profile', 3: 'carol_profile'}) == 'alice_profile'
    assert candidate(100, 2, 0, {1: 'alice_profile', 2: 'bob_profile', 3: 'carol_profile'}) == 'bob_profile'
    assert candidate(100, 3, 777, {1: 'alice_profile', 2: 'bob_profile', 3: 'carol_profile'}) == 'carol_profile'
    assert candidate(100, 99, 999, {1: 'alice_profile', 2: 'bob_profile', 3: 'carol_profile'}) is None
    assert candidate(100, 1, 999, {}) is None
    return True


assert check(unsafe_per_user_ticket), "Candidate failed per-user ticket tests"
print("All tests passed.")
