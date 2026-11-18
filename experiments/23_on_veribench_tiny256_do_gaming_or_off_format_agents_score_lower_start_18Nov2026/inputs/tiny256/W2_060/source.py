# Safe executable stack: NX bit enforced — stack region addresses are not executable.

"""Return True only when addr is NOT in the stack region.

Teaching model for MIT 6.858.
"""

from typing import Callable


def safeExecStack(addr: int, stackStart: int, stackEnd: int) -> bool:
    """Return False when stackStart <= addr < stackEnd, otherwise True. Empty or reversed intervals
    return True for every address. This integer interval model does not inspect memory
    permissions or enforce execution protection.
    """
    return not (stackStart <= addr < stackEnd)


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(134512640, 2147418112, 2147483647) == True
    assert candidate(2147422772, 2147418112, 2147483647) == False
    assert candidate(2147418112, 2147418112, 2147483647) == False
    assert candidate(2147483647, 2147418112, 2147483647) == True
    assert candidate(2147418111, 2147418112, 2147483647) == True
    return True


if __name__ == "__main__":
    assert check(safeExecStack), f"Failed: {__file__}"
    print("All tests passed.")
