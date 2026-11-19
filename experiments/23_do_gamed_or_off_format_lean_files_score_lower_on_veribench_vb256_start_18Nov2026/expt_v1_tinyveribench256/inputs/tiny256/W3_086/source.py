"""Return block.data, raising ValueError if block is not a MemoryBlock or has been freed."""

from typing import Callable


class MemoryBlock:
    """Simulated memory block holding a string and a freed flag."""
    def __init__(self, data: str):
        """Build a block holding data, not yet freed."""
        self.data = data
        self.is_freed = False

    def free(self):
        """Mark the block freed and clear its data."""
        self.is_freed = True
        self.data = None

    def is_valid(self) -> bool:
        """True iff the block has not been freed."""
        return not self.is_freed


def safe_access_memory(block: MemoryBlock) -> str:
    """Return block.data, raising ValueError if block is not a MemoryBlock or has been freed."""
    if not isinstance(block, MemoryBlock):
        raise ValueError("invalid block")
    if not block.is_valid():
        raise ValueError("access after free")
    # data can be empty string
    return block.data  # type: ignore[return-value]


def check(candidate: Callable[[MemoryBlock], str]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    b1 = MemoryBlock('hello')
    assert candidate(b1) == 'hello'
    b3 = MemoryBlock('')
    assert candidate(b3) == ''
    assert candidate(MemoryBlock('xy')) == 'xy'
    expired = MemoryBlock('data')
    expired.free()
    try:
        candidate(expired)
    except ValueError:
        pass
    else:
        raise AssertionError("expected ValueError")
    try:
        candidate(None)
    except ValueError:
        pass
    else:
        raise AssertionError("expected ValueError")
    return True


if __name__ == "__main__":
    assert check(safe_access_memory), f"Failed: {__file__}"
    print("All tests passed.")

