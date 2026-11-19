# Synthetic VeriBench task -- Inspired by: Patient/Sample Match Gate for Transfusion Safety (FDA 21 CFR 820)
# Original language: Python
# Category: 05_regulated
"""Synthetic identifier-match predicate combining equal nonnegative identifiers with a supplied
crossmatch-status flag, with a fixed test harness.
"""

from typing import Callable


def pre_condition(patient_id: int, sample_id: int, crossmatch_ok: bool) -> bool:
    """Return whether patient_id and sample_id are nonnegative."""
    return patient_id >= 0 and sample_id >= 0


def my_transfusion_match_ok(patient_id: int, sample_id: int, crossmatch_ok: bool) -> bool:
    """Return whether the patient and sample identifiers match and the crossmatch flag is set.
    Raise AssertionError if the input predicate rejects the arguments.

    The input check requires that patient_id and sample_id are nonnegative. A failed check
    raises AssertionError.
    """
    assert pre_condition(patient_id, sample_id, crossmatch_ok), "pre violated"
    return bool(patient_id == sample_id and crossmatch_ok)


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(42, 42, True) is True
    assert candidate(0, 0, True) is True
    assert candidate(42, 43, True) is False
    assert candidate(42, 42, False) is False
    try:
        candidate(-1, 0, True)
    except AssertionError:
        pass
    else:
        raise AssertionError('expected AssertionError')
    return True


if __name__ == "__main__":
    assert check(my_transfusion_match_ok)
    print(f"All tests passed: {__file__}!")
