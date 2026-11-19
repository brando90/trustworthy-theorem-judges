# Source: synthetic — Flight control gain scheduling via integer division
# Category: 04_aerospace


"""Flight-control gain scheduling: scales a maximum gain by the current airspeed fraction using integer division."""

def my_fcs_gain_schedule(airspeed: int, max_airspeed: int, max_gain: int) -> int:
    """Return (max_gain * airspeed) // max_airspeed (integer floor division).

    Pre: 0 < max_airspeed
    Scales the PID gain proportionally to the current airspeed fraction.

    Used e.g. to scale a flight-control PID gain with airspeed or to interpolate any gain
    against an operating-point fraction in integer arithmetic.

    Raise AssertionError unless max_airspeed is positive.
    """
    assert 0 < max_airspeed, "max_airspeed must be positive"
    return (max_gain * airspeed) // max_airspeed


def check() -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert my_fcs_gain_schedule(50, 100, 100) == 50
    assert my_fcs_gain_schedule(0, 100, 100) == 0
    assert my_fcs_gain_schedule(100, 100, 100) == 100
    assert my_fcs_gain_schedule(5, 10, 200) == 100
    assert my_fcs_gain_schedule(3, 10, 100) == 30
    return True


if __name__ == "__main__":
    assert check()
    print("All tests passed")
