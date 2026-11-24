"""Teaching model returning the supplied UID unchanged, regardless of initialization status. No
operating-system privileges are inspected or changed.
"""


def unsafe_privilege_drop(current_uid: int, init_done: bool) -> int:
    """Return current_uid unchanged, ignoring init_done. This teaching model returns a supplied
    integer. It does not inspect or change process privileges.
    """
    return current_uid  # init_done ignored — never drops privileges


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(0, True) == 0
    assert candidate(0, False) == 0
    assert candidate(1000, True) == 1000
    assert candidate(500, True) == 500
    assert candidate(33, False) == 33
    return True


assert check(unsafe_privilege_drop), "Candidate failed privilege drop tests"
print("All tests passed.")
