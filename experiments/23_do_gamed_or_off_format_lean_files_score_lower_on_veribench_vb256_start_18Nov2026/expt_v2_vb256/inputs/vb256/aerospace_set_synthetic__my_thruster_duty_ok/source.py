# Source: synthetic — Thruster duty cycle compliance check via cross-multiplied integer arithmetic
# Category: 04_aerospace


"""Compare on-time against a duty limit expressed in tenths using a scaled arithmetic comparison."""

def my_thruster_duty_ok(on_ms: int, period_ms: int, duty_pct: int) -> bool:
    """Return on_ms * 10 <= period_ms * duty_pct, where duty_pct expresses tenths of a period.
    Raise AssertionError unless period_ms > 0 and duty_pct <= 10. Integer types and non-negative
    on_ms or duty_pct are not enforced. Compatible non-integer numeric inputs are accepted.
    """
    assert 0 < period_ms, "period_ms must be positive"
    assert duty_pct <= 10, "duty_pct must be <= 10"
    return on_ms * 10 <= period_ms * duty_pct


def check() -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert my_thruster_duty_ok(50, 100, 5) == True
    assert my_thruster_duty_ok(0, 100, 10) == True
    assert my_thruster_duty_ok(60, 100, 5) == False
    assert my_thruster_duty_ok(100, 100, 10) == True
    assert my_thruster_duty_ok(1, 100, 0) == False
    return True


if __name__ == "__main__":
    assert check()
    print("All tests passed")
