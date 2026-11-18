# Unsafe secure boot — MIT 6.858 Lecture 18: IoT Security (Azure Sphere)
# Boots all stages without verifying their signatures — unsigned firmware executes.

"""Return True unconditionally without inspecting the supplied stages or verifying signatures."""

from typing import Optional


def unsafe_boot_chain(stages: list[tuple[int, int]]) -> bool:
    """Return True for any stages input, including an empty list. Stages nominally contains
    (firmware_hash, signature) pairs, but the input is never inspected. No signature
    verification or firmware execution occurs.
    """
    return True   # no verification — vulnerability!


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate([]) is True
    assert candidate([(43981, 43981)]) is True
    assert candidate([(43981, 0)]) is True
    assert candidate([(57005, 48879), (4660, 0)]) is True
    assert candidate([(49374, 65535), (47824, 0)]) is True
    return True


assert check(unsafe_boot_chain)
print("All tests passed.")
