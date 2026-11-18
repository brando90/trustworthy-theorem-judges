"""Model a status decision from supplied padding and authentication flags: return 0 when both are
truthy, otherwise 1. No TLS processing or cryptographic verification is performed.
"""


def safe_padding_oracle(padding_valid: bool, mac_valid: bool) -> int:
    """Return 0 when padding_valid and mac_valid are both truthy. Otherwise return 1. These are
    supplied flags, not results verified here. The shared failure value provides no timing
    guarantee.
    """
    if padding_valid and mac_valid:
        return 0
    return 1  # generic error — no distinguishing signal


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(True, True) == 0
    assert candidate(True, False) == 1
    assert candidate(False, False) == 1
    assert candidate(False, True) == 1
    assert candidate(padding_valid=False, mac_valid=False) == 1
    return True


assert check(safe_padding_oracle), "Candidate failed tests"
print("All tests passed.")
