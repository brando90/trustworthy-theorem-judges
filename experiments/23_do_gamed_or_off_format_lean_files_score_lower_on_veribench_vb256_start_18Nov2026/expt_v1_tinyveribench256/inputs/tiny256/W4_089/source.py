"""Return a server-log entry with the recipient ID and timestamp. Store None for the sender ID.

Teaching model for MIT 6.858.
"""
from typing import Callable


def safe_log(_sender: int, recipient: int, timestamp: int) -> dict:
    """Return a server-log entry with the recipient ID and timestamp. Store None for the sender ID."""
    return {"sender_id": None, "recipient_id": recipient, "timestamp": timestamp}


def adversary_read_sender(entry: dict) -> int | None:
    """The sender_id field of a log entry, or None if it is absent or hidden."""
    return entry.get("sender_id")


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(7, 8, 1700000000) == {"sender_id": None, "recipient_id": 8, "timestamp": 1700000000}
    assert candidate(0, 2, 0) == {"sender_id": None, "recipient_id": 2, "timestamp": 0}
    assert candidate(7, 8, 0) == {'sender_id': None, 'recipient_id': 8, 'timestamp': 0}
    assert candidate(1, 1, 1) == {'sender_id': None, 'recipient_id': 1, 'timestamp': 1}
    assert candidate(1, 8, 1700000000) == {'sender_id': None, 'recipient_id': 8, 'timestamp': 1700000000}
    return True


if __name__ == "__main__":
    assert check(safe_log), f"Failed: {__file__}"
    print("All tests passed.")
