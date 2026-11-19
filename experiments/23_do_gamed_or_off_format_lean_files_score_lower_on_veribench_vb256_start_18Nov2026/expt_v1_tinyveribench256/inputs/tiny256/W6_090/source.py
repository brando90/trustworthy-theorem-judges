# Unsafe certificate chain validation: accepts certificates without CA signature.

"""Toy certificate-chain check that returns True without inspecting the supplied certificate
authority signature value. No signature verification, chain validation, or request processing
occurs.
"""

def unsafe_cert_chain(ca_signature: int) -> bool:
    """Return True regardless of ca_signature. The supplied value is ignored. No certificate
    authority signature or certificate chain is verified.
    """
    return True


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(12345) is True
    assert candidate(0) is True
    assert candidate(1) is True
    assert candidate(2) is True
    assert candidate(3) is True
    return True


assert check(unsafe_cert_chain), "Candidate failed tests"
print("All tests passed.")
