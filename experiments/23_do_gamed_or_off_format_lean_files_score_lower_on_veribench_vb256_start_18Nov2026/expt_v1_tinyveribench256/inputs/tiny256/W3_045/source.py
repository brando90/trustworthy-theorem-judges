"""Model a Finished acceptance check using a supplied ChangeCipherSpec flag and an XOR-based value."""

from typing import Callable, List


def compute_finished_mac(messages: List[int], master_secret: int) -> int:
    """Compute the Finished MAC over a list of message IDs (simplified model).
    Returns XOR of all message IDs with the master_secret."""
    result = master_secret
    for msg in messages:
        result ^= msg
    return result


def safe_ssl_finished_check(
    received_messages: List[int],
    finished_mac: int,
    master_secret: int,
    change_cipher_spec_received: bool,
) -> bool:
    """Return False when change_cipher_spec_received is false. Otherwise, return whether
    finished_mac equals master_secret XOR every received message ID. The flag is trusted input,
    and the XOR calculation is a teaching model rather than cryptographic authentication.
    """
    # Fix: enforce that CCS must arrive before Finished
    if not change_cipher_spec_received:
        return False  # Reject Finished without prior ChangeCipherSpec
    expected_mac = compute_finished_mac(received_messages, master_secret)
    return finished_mac == expected_mac


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate([1, 2, 3, 4, 5], 43, 42, True) is True
    assert candidate([1, 2], 0, 42, True) is False
    assert candidate([], 42, 42, False) is False
    assert candidate([], 1, 1, True) is True
    assert candidate([1], 1, 1, True) is False
    return True


if __name__ == "__main__":
    assert check(safe_ssl_finished_check), f"Failed: {__file__}"
    print("All tests passed.")
