# Unsafe TLS certificate name validation: accepts any certificate regardless of name.

"""Toy certificate-name check that returns True without inspecting the supplied server and
certificate name values. No certificate validation or request processing occurs.
"""

def unsafe_tls_cert_name(server_name: int, cert_name: int) -> bool:
    """Return True regardless of server_name and cert_name. Neither input is inspected. No
    certificate-name validation is performed.
    """
    return True

def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(100, 100) is True
    assert candidate(200, 200) is True
    assert candidate(0, 0) is True
    assert candidate(100, 200) is True
    assert candidate(500, 999) is True
    return True

assert check(unsafe_tls_cert_name)
print("All tests passed.")
