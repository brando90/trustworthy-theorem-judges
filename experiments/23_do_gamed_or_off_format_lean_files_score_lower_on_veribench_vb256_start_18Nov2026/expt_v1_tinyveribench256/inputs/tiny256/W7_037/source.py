# Unsafe iOS App Entitlements Model (MIT 6.858 Lecture 9)
# Vulnerability: no entitlement check — any app gains access to any resource.

"""No check: all resource requests are granted unconditionally."""

from typing import List


def unsafe_app_entitlements(app_id: int, resource: str,
                             granted_entitlements: List[str]) -> bool:
    """No check: all resource requests are granted unconditionally."""
    return True  # Vulnerability: entitlement list is never consulted


def check() -> None:
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_app_entitlements(42, 'camera', []) is True
    assert unsafe_app_entitlements(1, 'contacts', ['location']) is True
    assert unsafe_app_entitlements(99, 'microphone', []) is True
    assert unsafe_app_entitlements(5, 'camera', []) is True
    assert unsafe_app_entitlements(0, '', []) is True


if __name__ == "__main__":
    check()
