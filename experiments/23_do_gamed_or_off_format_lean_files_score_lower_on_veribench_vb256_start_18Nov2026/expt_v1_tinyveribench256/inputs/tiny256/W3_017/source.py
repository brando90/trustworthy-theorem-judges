# Safe heap address validation: allows only addresses within [heap_base, heap_base+heap_size).

"""Returns True only when heap_base <= addr < heap_base + heap_size."""

def safe_heap_validate(addr: int, heap_base: int, heap_size: int) -> bool:
    """Return whether heap_base <= addr < heap_base + heap_size using integer arithmetic. Zero or
    negative heap_size yields False. This checks only the supplied bounds. It does not inspect
    memory mappings or establish pointer validity.
    """
    return heap_base <= addr < heap_base + heap_size


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_heap_validate(120, 100, 50) == True
    assert safe_heap_validate(100, 100, 50) == True
    assert safe_heap_validate(149, 100, 50) == True
    assert safe_heap_validate(0, 100, 50) == False
    assert safe_heap_validate(150, 100, 50) == False

if __name__ == "__main__":
    check()
