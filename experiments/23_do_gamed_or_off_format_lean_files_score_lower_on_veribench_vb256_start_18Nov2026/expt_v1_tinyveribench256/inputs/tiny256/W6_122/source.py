"""Toy passcode derivation using repeated arithmetic string transformations, ignoring the device
identifier. The returned offline-attack flag is supplied by the caller.
"""
import hashlib


def simple_hash(s: str) -> str:
    """Return a decimal string from the input length and character code points for use in the
    simulated protocol.
    """
    char_sum = 0
    for c in s:
        char_sum = char_sum + ord(c) * 31
    return str(len(s) * 37 + char_sum)


def unsafe_passcode_kdf(
    passcode: str, uid: str, iterations: int, can_extract_data: bool
) -> tuple[str, bool]:
    """Apply simple_hash to passcode iterations times and return (result, can_extract_data). Ignore
    uid. For zero or negative iterations, return the original passcode. This is a toy
    transformation. The supplied flag is copied without assessing offline brute-force
    capability.
    """
    key = passcode
    for _ in range(iterations):
        key = simple_hash(key)  # UID NOT mixed in -- vulnerability
    return (key, can_extract_data)  # offline attack mirrors data extraction


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    key1, offline1 = candidate('1234', 'device-uid', 100, False)
    assert offline1 is False
    key2, offline2 = candidate('1234', 'device-uid', 100, True)
    assert offline2 is True
    assert candidate('', '', 0, False) == ('', False)
    assert candidate('1', 'd', 1, True) == ('1556', True)
    assert candidate('1234', 'd', 100, True) == ('6689', True)
    return True


assert check(unsafe_passcode_kdf), "Candidate failed tests"
print("All tests passed.")
