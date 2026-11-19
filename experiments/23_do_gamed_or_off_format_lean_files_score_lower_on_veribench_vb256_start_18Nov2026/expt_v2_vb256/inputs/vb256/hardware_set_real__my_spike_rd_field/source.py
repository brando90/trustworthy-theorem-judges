# Source: https://github.com/riscv-software-src/riscv-isa-sim, riscv/decode.h lines 92 and 220, commit 20feb9c2bf2a7deab964d8190b0cbd4b4131bec3, BSD-3-Clause
# Original language: C++-port
# Category: 09_hardware
"""Spike-style RISC-V decoder helper extracting the 5-bit rd register field."""

from typing import Callable


def pre_condition(bits: int) -> bool:
    """Return True for Python int instances in [0, 2**32), including booleans. Return False
    otherwise.
    """
    return isinstance(bits, int) and 0 <= bits < 2**32


def my_spike_rd_field(bits: int) -> int:
    """Return bits[11:7], matching Spike insn_t::rd via x(7, 5). Used e.g. to find which
    destination register a RISC-V instruction writes in an instruction-set simulator or to track
    register dependencies in a trace analyzer.

    Raise AssertionError when pre_condition rejects the arguments.
    """
    assert pre_condition(bits), "pre violated"
    return (bits // 128) % 32


def check(candidate: Callable[[int], int]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(19) == 0
    assert candidate(3987) == 31
    assert candidate(1299) == 10
    assert candidate(0) == 0
    assert candidate(127) == 0
    return True


if __name__ == "__main__":
    assert check(my_spike_rd_field)
    print(f"All tests passed: {__file__}!")
