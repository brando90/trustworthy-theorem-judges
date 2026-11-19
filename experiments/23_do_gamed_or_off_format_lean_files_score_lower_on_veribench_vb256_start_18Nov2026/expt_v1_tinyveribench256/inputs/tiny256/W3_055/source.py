"""Compute a simulated privilege-drop UID result from supplied values without changing process
privileges.
"""

from typing import Callable


def safe_privilege_drop(current_uid: int, init_done: bool,
                        target_uid: int) -> int | None:
    """Return None if target_uid is zero. Otherwise, return target_uid when init_done is true and
    current_uid is zero. Return current_uid in all other cases. Negative integer UIDs are
    accepted. This computes a simulated result without changing process privileges.
    """
    if target_uid == 0:
        return None          # invalid: would remain/become root
    if init_done and current_uid == 0:
        return target_uid    # drop root after privileged setup
    return current_uid


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(0, True, 1000) == 1000
    assert candidate(0, False, 1000) == 0
    assert candidate(500, True, 1000) == 500
    assert candidate(0, True, 33) == 33
    assert candidate(0, True, 65534) == 65534
    return True


if __name__ == "__main__":
    assert check(safe_privilege_drop), f"Failed: {__file__}"
    print("All tests passed.")
