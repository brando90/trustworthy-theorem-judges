"""Return True when the required receiver permission is zero or appears in the supplied held
permissions. Otherwise return False. This model does not send a broadcast.
"""


def safe_broadcast_send(
    intent_action: int,
    required_receiver_perm: int,
    receiver_held_perms: list,
) -> bool:
    """Return True if required_receiver_perm is zero or belongs to receiver_held_perms. Otherwise
    return False. Zero denotes unrestricted access. intent_action is ignored. This function only
    computes a boolean decision and does not deliver a broadcast.
    """
    if required_receiver_perm == 0:
        return True
    return required_receiver_perm in receiver_held_perms


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(1, 10, [10, 20]) is True
    assert candidate(1, 10, []) is False
    assert candidate(2, 99, [1, 2]) is False
    assert candidate(3, 0, []) is True
    assert candidate(5, 100, []) is False
    return True


assert check(safe_broadcast_send), "Candidate failed tests"
print("All tests passed.")
