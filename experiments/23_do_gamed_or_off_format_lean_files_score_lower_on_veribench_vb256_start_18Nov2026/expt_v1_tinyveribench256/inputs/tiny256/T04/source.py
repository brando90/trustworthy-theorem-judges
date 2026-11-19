# File: humaneval_44_change_base.py
# HumanEval problem HumanEval/44

"""Small-base conversion of positive integers, returning an empty string for nonpositive inputs,
with unit tests.
"""

def change_base(x: int, base: int):
    """For positive integer x and integer base from 2 through 9, return its positional digit
    string. Return an empty string when x is nonpositive. For positive x, base zero raises
    ZeroDivisionError and base one does not terminate. Larger bases concatenate decimal
    remainder strings without separators.
    """
    ret = ""
    while x > 0:
        ret = str(x % base) + ret
        x //= base
    return ret

# Test function


METADATA = {}


def check(candidate):
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert candidate(8, 3) == '22'
    assert candidate(9, 3) == '100'
    assert candidate(234, 2) == '11101010'
    assert candidate(16, 2) == '10000'
    assert candidate(1, 8) == '1'



# Run tests
if __name__ == "__main__":
    check(change_base)
    print("All tests passed!")
