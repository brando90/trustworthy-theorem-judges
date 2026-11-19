# Safe iOS App Entitlements Model (MIT 6.858 Lecture 9)
# Fix: access is granted only when the resource key is in the Apple-signed entitlement list.

"""Model an entitlement decision using resource membership in a supplied list. The list is trusted
input. Signatures and application ownership are not verified.
"""

from typing import List


def safe_app_entitlements(app_id: int, resource: str,
                           granted_entitlements: List[str]) -> bool:
    """Return whether resource appears in granted_entitlements using exact string equality. app_id
    is ignored. The supplied list is trusted. No signature or association with the application
    is verified.
    """
    return resource in granted_entitlements


def check() -> None:
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_app_entitlements(1, 'camera', ['camera', 'microphone']) is True
    assert safe_app_entitlements(2, 'contacts', ['camera']) is False
    assert safe_app_entitlements(3, 'location', []) is False
    assert safe_app_entitlements(1, 'cam', ['camera']) is False
    assert safe_app_entitlements(1, 'location', ['camera', 'microphone', 'location']) is True


if __name__ == "__main__":
    check()
