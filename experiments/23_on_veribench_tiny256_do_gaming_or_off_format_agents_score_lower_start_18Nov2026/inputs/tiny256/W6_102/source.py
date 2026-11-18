"""Write the raw app_ptr directly into the selected shared buffer slot. Return False for an invalid
slot, or True after the write.

Teaching model for MIT 6.858.
"""


def unsafe_tainted_ptr(app_ptr: int, shared_buf: list[int], slot: int) -> bool:
    """Write the raw app_ptr directly into the selected shared buffer slot. Return False for an
    invalid slot, or True after the write.
    """
    if slot < 0 or slot >= len(shared_buf):
        return False
    shared_buf[slot] = app_ptr  # raw pointer value leaked to sandbox (vulnerability)
    return True


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    app_ptr = 140734438775808
    buf = [0] * 8
    result = candidate(app_ptr, buf, 0)
    assert result is True
    buf2 = [0] * 4
    result = candidate(3735928559, buf2, 2)
    assert result is True
    buf3 = [0] * 2
    result = candidate(app_ptr, buf3, 5)
    assert result is False
    result = candidate(app_ptr, buf3, -1)
    assert result is False
    result = candidate(app_ptr, [], 0)
    assert result is False
    return True


assert check(unsafe_tainted_ptr), "Candidate failed tests"
print("All tests passed.")
