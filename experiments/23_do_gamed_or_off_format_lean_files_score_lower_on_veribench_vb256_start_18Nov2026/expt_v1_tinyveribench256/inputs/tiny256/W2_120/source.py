# Safe plaintext file system: files encrypted with client key; server access requires matching key.

"""Returns True only when server_key equals the file encryption key."""

def safe_file_access(file_key: int, server_key: int) -> bool:
    """Return True when file_key equals server_key, otherwise False. This toy key comparison
    performs no encryption, decryption, file access, or access enforcement.
    """
    return file_key == server_key


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_file_access(100, 100) == True
    assert safe_file_access(100, 999) == False
    assert safe_file_access(42, 0) == False
    assert safe_file_access(0, 0) == True
    assert safe_file_access(1, 0) is False

if __name__ == "__main__":
    check()
