
"""Model a stack-depth limit with an integer comparison. No stack is inspected or controlled."""

def safe_wasm_stack(stack_depth: int, max_depth: int) -> bool:
    """Return whether stack_depth is at most max_depth. Negative inputs are compared without
    additional validation. No stack limit is enforced.
    """
    return stack_depth <= max_depth


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_wasm_stack(5, 100) == True
    assert safe_wasm_stack(100, 100) == True
    assert safe_wasm_stack(101, 100) == False
    assert safe_wasm_stack(9999, 10) == False
    assert safe_wasm_stack(0, 0) == True

if __name__ == "__main__":
    check()
