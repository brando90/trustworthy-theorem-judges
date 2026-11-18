# Unsafe RSA exponentiation: computes m^d mod n directly without Montgomery blinding, leaking timing.

"""Compute pow(message, d, n) directly, without blinding. Negative exponents require a modular
inverse. Zero modulus or a missing required inverse raises ValueError. A separate status
function always returns False.
"""

def unsafe_rsa_decrypt(message: int, d: int, n: int) -> int:
    """Return pow(message, d, n), using Python's integer modular exponentiation directly. Negative
    moduli are supported. Negative exponents require an inverse modulo n. A missing required
    inverse or zero modulus raises ValueError. No blinding is performed.
    """
    return pow(message, d, n)


def unsafe_blinding_applied(message: int, d: int, n: int) -> bool:
    """Returns False: no blinding is applied in this unsafe version."""
    return False


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_blinding_applied(2, 3, 35) == False
    assert unsafe_blinding_applied(0, 0, 1) == False
    assert unsafe_blinding_applied(2, 3, 0) is False
    assert unsafe_blinding_applied(1, 1, 1) is False
    assert unsafe_blinding_applied(2, 2, 2) is False

if __name__ == "__main__":
    check()
