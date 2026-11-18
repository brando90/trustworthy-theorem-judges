"""Simulate a memory block with data and a freed flag. Freeing clears data to None.
unsafe_access_memory returns the current data attribute without checking the freed flag.
"""

class MemoryBlock:
    """Simulated memory block holding a string and a freed flag."""
    def __init__(self, data: str):
        """Build a block holding data, not yet freed."""
        self.data = data
        self.is_freed = False
    
    def free(self):
        """Set is_freed to True and clear data to None."""
        self.is_freed = True
        self.data = None
    
    def is_valid(self) -> bool:
        """Check if the memory block is still valid (not freed)"""
        return not self.is_freed

def unsafe_access_memory(block: MemoryBlock) -> str:
    """Return block.data without checking block.is_freed. For a MemoryBlock whose data has not been
    changed after free(), return None.
    """
    return block.data


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    block1 = MemoryBlock('hello world')
    assert candidate(block1) == 'hello world'
    block2 = MemoryBlock('test data')
    block2.free()
    assert candidate(block2) is None
    block3 = MemoryBlock('first')
    block4 = MemoryBlock('second')
    block3.free()
    assert candidate(block3) is None
    assert candidate(block4) == 'second'
    block5 = MemoryBlock('repeated')
    block5.free()
    assert candidate(block5) is None
    return True


assert check(unsafe_access_memory), "Candidate failed use-after-free tests"
print("All tests passed.")
