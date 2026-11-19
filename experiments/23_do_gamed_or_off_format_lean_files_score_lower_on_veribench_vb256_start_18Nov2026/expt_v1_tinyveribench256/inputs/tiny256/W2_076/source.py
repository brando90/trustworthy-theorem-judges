# Safe OCSP stapling: server pre-fetches OCSP response; CA never contacted by browser.

"""Return (accepted, False) for the modeled stapled status response, with accepted set when
stapled_response is positive.
"""

def safe_ocsp_stapled(cert_serial: int, stapled_response: int, server_domain: int) -> tuple:
    """Return (accepted, False) for the modeled stapled status response, with accepted set when
    stapled_response is positive.
    """
    cert_valid = stapled_response > 0
    ca_learns_visit = False  # CA never contacted during the user's visit
    return cert_valid, ca_learns_visit


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(123, 1, 456) == (True, False)
    assert candidate(123, 0, 456) == (False, False)
    assert candidate(999, 100, 1) == (True, False)
    assert candidate(0, 0, 0) == (False, False)
    assert candidate(1, 1, 1) == (True, False)
    return True

assert check(safe_ocsp_stapled)
print("All tests passed.")
