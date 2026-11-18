# Safe stack canary check: verifies canary matches expected value before returning success.

"""Returns True only when canary equals expected_canary."""

def safe_stack_canary_bypass(user_data: str, canary: int, expected_canary: int) -> bool:
    """Return True when canary equals expected_canary, otherwise False. user_data is ignored. This
    comparison does not inspect stack memory or establish that exploitation was prevented.
    """
    return canary == expected_canary


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_stack_canary_bypass('hello', 3735928559, 3735928559) == True
    assert safe_stack_canary_bypass('data', 12345, 12345) == True
    assert safe_stack_canary_bypass('overflow_payload', 1094795585, 3735928559) == False
    assert safe_stack_canary_bypass('exploit', 0, 3735928559) == False
    assert safe_stack_canary_bypass('', 0, 0) is True

if __name__ == "__main__":
    check()
