# Synthetic VeriBench task — Inspired by: axi valid/ready fire predicate
# Original language: Python
# Category: 09_hardware
"""AXI-style handshake detector: a transfer fires exactly when valid and ready are both asserted."""

from typing import Callable


def pre_condition(valid: bool, ready: bool) -> bool:
    """Return whether valid and ready are Boolean."""
    return isinstance(valid, bool) and isinstance(ready, bool)


def my_axi_valid_ready_fire(valid: bool, ready: bool):
    """AXI-style handshake detector: a transfer fires exactly when valid and ready are both
    asserted. Used e.g. to decide in a bus monitor or testbench whether an AXI channel transfers
    a beat in this cycle or to count completed transfers.

    The input check requires that valid and ready are Boolean. A failed check raises
    AssertionError.
    """
    assert pre_condition(valid, ready), "pre violated"
    return valid and ready


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(True, True) is True
    assert candidate(True, False) is False
    assert candidate(False, True) is False
    assert candidate(False, False) is False
    try:
        candidate(None, False)
    except AssertionError:
        pass
    else:
        raise AssertionError("expected AssertionError")
    return True


if __name__ == "__main__":
    assert check(my_axi_valid_ready_fire)
    print(f"All tests passed: {__file__}!")
