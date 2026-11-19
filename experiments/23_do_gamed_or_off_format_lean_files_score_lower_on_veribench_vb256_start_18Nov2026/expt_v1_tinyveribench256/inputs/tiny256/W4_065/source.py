"""Binder permission-decision model: return True when caller_uid belongs to authorized_uids and
required_permission belongs to granted_permissions. Otherwise return False. service_id is
ignored, and no service is invoked.
"""

from typing import Callable, List


def safe_binder_call(
    service_id: int,
    caller_uid: int,
    required_permission: int,
    authorized_uids: List[int],
    granted_permissions: List[int]
) -> bool:
    """Return True when caller_uid is in authorized_uids and required_permission is in
    granted_permissions. Otherwise return False. service_id is ignored. No service is invoked.
    """
    # UID enforcement: check if caller UID is authorized
    if caller_uid not in authorized_uids:
        return False  # Unauthorized UID — deny

    # Permission enforcement: check if caller holds required permission
    if required_permission not in granted_permissions:
        return False  # Missing permission — deny

    # Both checks passed — allow service invocation
    return True


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(100, 1000, 1, [1000, 2000], [1, 2]) == True
    assert candidate(100, 9999, 1, [1000, 2000], [1, 2]) == False
    assert candidate(100, 1000, 999, [1000, 2000], [1, 2]) == False
    assert candidate(100, 0, 1, [1000, 2000], [1, 2]) == False
    assert candidate(100, 0, 1, [0, 1000], [1, 2]) == True
    return True


if __name__ == "__main__":
    assert check(safe_binder_call), f"Failed: {__file__}"
