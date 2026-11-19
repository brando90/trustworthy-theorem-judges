# Synthetic VeriBench task — Inspired by: aerospace redundant avionics bus selector
# Original language: Python
# Category: 04_aerospace
# Lines: ~70
"""Returns the primary command when its health flag is True, otherwise the backup command when its
health flag is True, otherwise False.
"""

from typing import Callable


def pre_condition(primaryHealthy, backupHealthy, primaryCmd, backupCmd) -> bool:
    """Return True exactly when all four arguments are instances of bool."""
    return all(isinstance(x, bool) for x in [primaryHealthy, backupHealthy, primaryCmd, backupCmd])


def my_redundant_bus_select(primaryHealthy, backupHealthy, primaryCmd, backupCmd) -> bool:
    """Return primaryCmd if primaryHealthy is True. Otherwise return backupCmd if backupHealthy is
    True. Otherwise return False. All four arguments must be bool instances, or AssertionError
    is raised. Health flags are supplied inputs. This function does not assess channel health.
    """
    assert pre_condition(primaryHealthy, backupHealthy, primaryCmd, backupCmd), "all inputs must be Boolean avionics channels"
    return (primaryCmd if primaryHealthy else (backupCmd if backupHealthy else False))


def check(candidate: Callable[..., bool]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(True, True, True, False) is True
    assert candidate(False, True, True, False) is False
    assert candidate(False, True, True, True) is True
    assert candidate(False, False, True, True) is False
    assert candidate(True, False, True, True) is True
    return True


if __name__ == "__main__":
    assert check(my_redundant_bus_select)
    print(f"All tests passed: {__file__}!")
