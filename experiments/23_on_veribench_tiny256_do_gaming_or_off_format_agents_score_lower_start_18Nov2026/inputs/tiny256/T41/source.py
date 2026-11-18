# File: humaneval_50_encode_shift.py
# HumanEval problem HumanEval/50

"""Shift cipher encoding and decoding of lowercase strings (shift by 5), with unit tests."""

def encode_shift(s: str):
    """Map each character to the lowercase ASCII letter at index (ord(character) - ord('a') + 5)
    modulo 26. For lowercase ASCII input, this shifts letters forward by five with wraparound.
    Return an empty string for empty input.
    """
    return "".join([chr(((ord(ch) + 5 - ord("a")) % 26) + ord("a")) for ch in s])


def decode_shift(s: str):
    """Map each character to the lowercase ASCII letter at index (ord(character) - ord('a') - 5)
    modulo 26. This recovers the original from encode_shift only when the original consists of
    lowercase ASCII letters. Return an empty string for empty input.
    """
    return "".join([chr(((ord(ch) - 5 - ord("a")) % 26) + ord("a")) for ch in s])

# Test function


METADATA = {}


def check(candidate):
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert candidate("mjqqt") == "hello"
    assert candidate("abc") == "vwx"
    assert candidate("") == ""
    assert candidate('m') == 'h'
    assert encode_shift('owl') == 'tbq'



# Run tests
if __name__ == "__main__":
    check(decode_shift)
    print("All tests passed!")
