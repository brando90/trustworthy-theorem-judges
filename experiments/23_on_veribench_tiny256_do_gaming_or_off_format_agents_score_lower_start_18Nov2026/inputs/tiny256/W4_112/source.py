# Unsafe RSA timing: execution time varies with the key bit (Kocher timing attack).

"""Return the modeled RSA multiplication count for the supplied key bit: two for a set bit, one for
a clear bit.
"""

def unsafeRSAMult(key_bit: bool) -> int:
    """Return the modeled RSA multiplication count for the supplied key bit: two for a set bit, one
    for a clear bit.
    """
    return 2 if key_bit else 1


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafeRSAMult(True) == 2
    assert unsafeRSAMult(False) == 1
    assert unsafeRSAMult(key_bit=False) == 1
    assert unsafeRSAMult(key_bit=True) == 2
    try:
        unsafeRSAMult()
    except TypeError:
        pass
    else:
        raise AssertionError("expected TypeError")

if __name__ == "__main__":
    check()
