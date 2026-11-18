# Safe BitLocker BIOS check: rejects USB inputs that exceed the BIOS buffer size.

"""Returns True only when usb_input_len does not exceed bios_buf_size."""

def safe_bitlocker_bios(usb_input_len: int, bios_buf_size: int, tpm_sealed: bool) -> bool:
    """Return whether usb_input_len <= bios_buf_size. Equality returns True. Negative integers are
    compared without validation. tpm_sealed is ignored. This toy guard performs no BIOS
    operation, TPM operation, or key protection.
    """
    return usb_input_len <= bios_buf_size


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_bitlocker_bios(64, 256, True) == True
    assert safe_bitlocker_bios(256, 256, True) == True
    assert safe_bitlocker_bios(257, 256, True) == False
    assert safe_bitlocker_bios(512, 256, True) == False
    assert safe_bitlocker_bios(9999, 256, False) == False

if __name__ == "__main__":
    check()
