"""Copy src bytes into dst at matching indices, leaving any remaining destination suffix unchanged.
Return None on success. If src is longer than dst, overwrite the available destination prefix,
then raise IndexError.
"""

def unsafe_copy(dst: bytearray, src: bytearray) -> None:
    """Copy src bytes into dst at matching indices, leaving any remaining destination suffix
    unchanged. Return None on success. If src is longer than dst, overwrite the available
    destination prefix, then raise IndexError.
    """
    for i, b in enumerate(src):
        dst[i] = b


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    d = bytearray(3)
    s = bytearray(b'abc')
    candidate(d, s)
    assert bytes(d) == b'abc'
    d2 = bytearray(2)
    s2 = bytearray(b'xy')
    candidate(d2, s2)
    assert bytes(d2) == b'xy'
    d4 = bytearray(b'hello')
    candidate(d4, bytearray())
    assert bytes(d4) == b'hello'
    buffer = bytearray(b'zip')
    candidate(buffer, bytearray(b't'))
    assert bytes(buffer) == b'tip'
    try:
        candidate(bytearray(1), bytearray(b'ab'))
    except IndexError:
        pass
    else:
        raise AssertionError("expected IndexError")
    return True

assert check(unsafe_copy), "Candidate failed buffer‐overflow tests"
print("All tests passed.")
