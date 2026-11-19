"""Toy compromise model that returns the supplied long_term_key_compromised flag unchanged. No key
exchange or session decryption is performed.
"""


def unsafe_static_key_exchange(long_term_key_compromised: bool) -> bool:
    """Return long_term_key_compromised unchanged. This is a toy Boolean model of compromise
    status. It performs no key derivation or decryption.
    """
    return long_term_key_compromised


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(True) is True
    assert candidate(False) is False
    assert candidate(long_term_key_compromised=False) is False
    assert candidate(long_term_key_compromised=True) is True
    try:
        candidate()
    except TypeError:
        pass
    else:
        raise AssertionError("expected TypeError")
    return True


assert check(unsafe_static_key_exchange), "Candidate failed tests"
print("All tests passed.")
