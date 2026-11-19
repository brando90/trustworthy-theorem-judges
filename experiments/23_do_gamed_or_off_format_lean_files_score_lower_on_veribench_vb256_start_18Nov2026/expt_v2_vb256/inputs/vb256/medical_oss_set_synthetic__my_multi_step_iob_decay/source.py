# Source: synthetic — multi-step insulin action model with 3-factor multiplication
# Category: medical_oss
"""Synthetic integer calculation scaling dose by steps and rate, divided by period times 100."""


def my_multi_step_iob_decay(dose: int, steps: int, rate: int, period: int) -> int:
    """Return (dose * steps * rate) // (period * 100). Raise AssertionError unless all arguments
    are nonnegative integers and period is positive. Booleans pass the integer checks. Neither
    steps nor rate has an upper bound.
    """
    assert all(isinstance(x, int) and x >= 0 for x in [dose, steps, rate, period])
    assert period > 0, "period must be positive"
    return (dose * steps * rate) // (period * 100)


def check() -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert my_multi_step_iob_decay(100, 2, 50, 1) == 100
    assert my_multi_step_iob_decay(0, 5, 80, 2) == 0
    assert my_multi_step_iob_decay(50, 0, 80, 2) == 0
    assert my_multi_step_iob_decay(50, 4, 0, 2) == 0
    assert my_multi_step_iob_decay(10, 3, 100, 1) == 30
    return True


if __name__ == "__main__":
    assert check()
    print("All tests passed")
