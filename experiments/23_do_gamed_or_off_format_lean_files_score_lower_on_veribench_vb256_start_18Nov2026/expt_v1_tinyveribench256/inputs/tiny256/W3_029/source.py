# TLDR: Safe kernel address leak fix — returns kernel virtual address only to privileged callers.

"""Return kernel_addr when caller_privilege equals KERNEL_PRIVILEGE (1). Otherwise return
REDACTED_ADDR (0). Privilege is supplied by the caller and is not authenticated.
"""

KERNEL_PRIVILEGE = 1
USER_PRIVILEGE = 0
REDACTED_ADDR = 0


def safeKernelAddrLeak(caller_privilege: int, kernel_addr: int) -> int:
    """Return kernel_addr when caller_privilege equals KERNEL_PRIVILEGE (1). Otherwise return
    REDACTED_ADDR (0). This function trusts the supplied privilege value.
    """
    if caller_privilege == KERNEL_PRIVILEGE:
        return kernel_addr
    return REDACTED_ADDR


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safeKernelAddrLeak(1, 18446603336221196288) == 18446603336221196288
    assert safeKernelAddrLeak(1, 18446744071578845184) == 18446744071578845184
    assert safeKernelAddrLeak(0, 18446603336221196288) == 0
    assert safeKernelAddrLeak(0, 18446744071578845184) == 0
    assert safeKernelAddrLeak(0, 0) == 0


if __name__ == "__main__":
    check()
