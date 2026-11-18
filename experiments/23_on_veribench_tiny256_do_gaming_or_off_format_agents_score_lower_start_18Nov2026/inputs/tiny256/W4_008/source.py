"""Compute an effective address using a zero-extended 32-bit offset.

Teaching model for MIT 6.858.
"""


def safe_wasm_zero_extend(mem_base: int, raw_u32_offset: int, mem_size: int) -> int | None:
    """Compute an effective address using a zero-extended 32-bit offset.

    Zero-extension: the offset is treated as an unsigned 32-bit integer (masked to
    32 bits), then added to mem_base.  The result is bounds-checked against
    [mem_base, mem_base + mem_size).  Returns the effective address on success,
    None if the access would be out-of-bounds.
    """
    zero_ext_offset = raw_u32_offset & 0xFFFFFFFF  # force unsigned 32-bit
    effective = mem_base + zero_ext_offset
    if effective < mem_base or effective >= mem_base + mem_size:
        return None  # out of sandbox — trap
    return effective


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(8589934592, 16, 4294967296) == 8589934608
    assert candidate(8589934592, 0, 4294967296) == 8589934592
    assert candidate(8589934592, 4096, 4096) is None
    assert candidate(0, 0, 0) is None
    assert candidate(1, 16, 4294967296) == 17
    return True


assert check(safe_wasm_zero_extend), "Candidate failed tests"
print("All tests passed.")
