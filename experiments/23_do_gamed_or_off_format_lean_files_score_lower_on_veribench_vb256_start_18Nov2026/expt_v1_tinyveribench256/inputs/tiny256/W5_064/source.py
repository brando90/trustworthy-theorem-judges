# Unsafe BitLocker BIOS check: does not detect that a BIOS buffer overflow can extract the TPM key.

"""Approve the request without checking whether a BIOS buffer overflow enables TPM key extraction."""

def unsafe_bitlocker_bios(usb_input_len: int, bios_buf_size: int, tpm_sealed: bool) -> bool:
    """Approve the request without checking whether a BIOS buffer overflow enables TPM key
    extraction.

    MIT 6.858 Fall 2012 Quiz 2: BIOS buffer overflow on stolen laptop extracts BitLocker key.
    """
    return True  # vulnerable: BIOS input length never validated


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_bitlocker_bios(64, 256, True) == True
    assert unsafe_bitlocker_bios(512, 256, True) == True
    assert unsafe_bitlocker_bios(9999, 256, False) == True
    assert unsafe_bitlocker_bios(0, 256, True) == True
    assert unsafe_bitlocker_bios(0, 0, True) is True

if __name__ == "__main__":
    check()
