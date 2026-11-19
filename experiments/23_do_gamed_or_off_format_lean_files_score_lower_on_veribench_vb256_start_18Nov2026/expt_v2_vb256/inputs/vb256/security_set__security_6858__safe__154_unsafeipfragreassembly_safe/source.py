# Safe IP fragment reassembly: rejects fragments whose byte ranges overlap existing data.

"""Check fragment byte ranges for overlaps. Return a Boolean without assembling or inspecting
payload data.
"""

from typing import List, Tuple


def safe_reassemble(fragments: List[Tuple[int, int, bytes]]) -> bool:
    """Return False if fragment ranges repeat any integer byte position. Otherwise return True.
    Each fragment supplies (offset, length, data), but data is ignored. Nonpositive lengths
    contribute no positions. Negative offsets are allowed. No payload is assembled.
    """
    received: set = set()
    for (offset, length, _data) in fragments:
        for byte_pos in range(offset, offset + length):
            if byte_pos in received:
                return False  # overlap detected — reject
            received.add(byte_pos)
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_reassemble([(0, 2, b"ab"), (1, 1, b"c")]) is False
    assert safe_reassemble([(0, 2, b"ab")]) is True
    assert safe_reassemble([]) == True
    assert safe_reassemble([(1, 1, b'c')]) is True
    assert safe_reassemble([(1, 1, b'c'), (0, 2, b'ab')]) is False

if __name__ == "__main__":
    check()
