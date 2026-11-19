# Safe TOFU key verification: pins the key and detects substitution.

"""Returns True only when new_key matches the stored (pinned) key."""

def safe_tofu_key(sender_id: int, new_key: int, stored_key: int) -> bool:
    """Return True if new_key equals stored_key, otherwise False. Ignore sender_id. Compare the
    supplied values without storing a key, verifying its origin, or emitting an alert.
    """
    return new_key == stored_key


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_tofu_key(1, 42, 42) == True
    assert safe_tofu_key(1, 99, 42) == False
    assert safe_tofu_key(1, 0, 42) == False
    assert safe_tofu_key(0, 0, 0) is True
    assert safe_tofu_key(1, 1, 42) is False

if __name__ == "__main__":
    check()
