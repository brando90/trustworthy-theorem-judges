# Synthetic VeriBench task - Inspired by: financial exchange and clearing-house invariants
# Original language: Python
# Category: finance
# Lines: 36
"""Return False for a repeated spend of the same output. Return True for the other flag combinations."""

from typing import Callable


def pre_condition(seen_again: bool, same_output: bool) -> bool:
    """Return whether seen_again and same_output are Boolean."""
    return isinstance(seen_again, bool) and isinstance(same_output, bool)


def my_utxo_double_spend_reject(seen_again: bool, same_output: bool):
    """Return False for a repeated spend of the same output. Return True for the other flag
    combinations.

    The input check requires that seen_again and same_output are Boolean. A failed check raises
    AssertionError.
    """
    assert pre_condition(seen_again, same_output), "pre violated"
    return not (seen_again and same_output)


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(False, False) is True
    assert candidate(True, False) is True
    assert candidate(False, True) is True
    assert candidate(True, True) is False
    try:
        candidate(None, False)
    except AssertionError:
        pass
    else:
        raise AssertionError("expected AssertionError")
    return True


if __name__ == "__main__":
    assert check(my_utxo_double_spend_reject)
    print(f"All tests passed: {__file__}!")
