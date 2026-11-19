"""Model read permission by testing only offset < pkt_len. Ignore length and accept negative
offsets whenever the comparison succeeds. No bytes are read.
"""


def unsafe_bpf_oob_read(offset: int, length: int, pkt_len: int) -> bool:
    """Return True exactly when offset < pkt_len, otherwise False. Ignore length and impose no
    nonnegative bounds on the integer arguments. This computes a permission flag without reading
    data.
    """
    if offset < pkt_len:            # only start offset checked — incomplete
        return True                 # read permitted
    return False                    # offset already out-of-range


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(0, 4, 20) == True
    assert candidate(18, 4, 20) == True
    assert candidate(20, 4, 20) == False
    assert candidate(0, 100, 20) == True
    assert candidate(5, 0, 20) == True
    return True


assert check(unsafe_bpf_oob_read), "Candidate failed tests"
print("All tests passed.")
