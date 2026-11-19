# Source: https://github.com/openaps/oref0, lib/determine-basal/determine-basal.js, 88cf032aa74ff25f69464a7d9cd601ee3940c0b3, MIT
# Original language: JavaScript-port
# Category: medical_oss
"""Compute a glucose target scaled by 100 using a multiplier of at least 110 percent, capped at
20000.
"""

def my_noisy_cgm_target_raise(target_bg, multiplier_percent) -> int:
    """Return min(20000, target_bg * max(110, multiplier_percent)), representing the adjusted
    target scaled by 100. The cap can reduce targets already above 200 mg/dL. Raise
    AssertionError unless both inputs are nonnegative Python integers. Booleans are accepted.
    """
    assert all(isinstance(x, int) and x >= 0 for x in [target_bg, multiplier_percent]), "inputs must be non-negative integers"
    effective_multiplier = max(110, multiplier_percent)
    return min(20000, target_bg * effective_multiplier)

def pre_condition(target_bg, multiplier_percent) -> bool:
    """True iff target_bg and multiplier_percent are both non-negative ints."""
    return all(isinstance(x, int) and x >= 0 for x in [target_bg, multiplier_percent])

from typing import Callable

def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(100, 100) == 11000
    assert candidate(120, 130) == 15600
    assert candidate(190, 110) == 20000
    assert candidate(80, 90) == 8800
    try:
        candidate(-1, 110)
    except AssertionError:
        pass
    else:
        raise AssertionError('expected AssertionError')
    return True

if __name__ == "__main__":
    assert check(my_noisy_cgm_target_raise)
    print(f"All tests passed: {__file__}!")
