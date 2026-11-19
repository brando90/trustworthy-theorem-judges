# Safe chroot UID isolation check: requires services to have distinct UIDs.

"""Returns True only when service_uid differs from other_uid."""

def safe_chroot_uid(service_uid: int, other_uid: int, chroot_dir: str, other_dir: str) -> bool:
    """Return whether service_uid differs from other_uid. Both directory arguments are ignored.
    This predicate does not change privileges or establish service isolation.
    """
    return service_uid != other_uid


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_chroot_uid(1001, 1002, '/jail/svc_a', '/jail/svc_b') == True
    assert safe_chroot_uid(500, 999, '/a', '/b') == True
    assert safe_chroot_uid(1001, 1001, '/jail/svc_a', '/jail/svc_b') == False
    assert safe_chroot_uid(0, 0, '/jail/svc_a', '/jail/svc_b') == False
    assert safe_chroot_uid(500, 500, '/a', '/b') == False

if __name__ == "__main__":
    check()
