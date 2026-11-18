# TLDR: Vulnerable kernel address leak — returns kernel virtual address to userspace without privilege check.

"""Return the supplied kernel_addr unchanged, ignoring caller_privilege. This integer passthrough
models an unchecked address disclosure. It does not obtain kernel addresses or demonstrate an
exploit.
"""

def unsafeKernelAddrLeak(caller_privilege: int, kernel_addr: int) -> int:
    """Return kernel_addr unchanged for any caller_privilege. Neither argument is validated.
    Kernel_addr is treated as a supplied integer, without checking whether it represents a
    kernel address.
    """
    return kernel_addr  # vulnerability: no privilege check


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafeKernelAddrLeak(1, 18446603336221196288) == 18446603336221196288
    assert unsafeKernelAddrLeak(1, 18446744071578845184) == 18446744071578845184
    assert unsafeKernelAddrLeak(0, 18446744071578845184) == 18446744071578845184
    assert unsafeKernelAddrLeak(0, 0) == 0
    assert unsafeKernelAddrLeak(0, 3735928559) == 3735928559


if __name__ == "__main__":
    check()
