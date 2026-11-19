"""Model a firmware acceptance decision by returning a supplied signature-validity flag, ignoring
both ECID values. No signature verification or boot operation is performed.
"""


def unsafe_boot_ecid(
    signature_valid: bool,
    firmware_ecid: int,
    device_ecid: int,
) -> bool:
    """Return signature_valid unchanged, ignoring firmware_ecid and device_ecid. This boolean model
    trusts the supplied flag. It performs no signature verification or firmware boot.
    """
    return signature_valid   # device binding NOT checked (vulnerability)


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(True, 43981, 43981) is True
    assert candidate(True, 4369, 43981) is True
    assert candidate(False, 43981, 43981) is False
    assert candidate(False, 4369, 43981) is False
    assert candidate(True, 0, 65535) is True
    return True


assert check(unsafe_boot_ecid), "Candidate failed tests"
print("All tests passed.")
