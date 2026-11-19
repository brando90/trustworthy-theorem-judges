# File: humaneval_27_flip_case.py
# HumanEval problem HumanEval/27

"""Swap the case of every letter in a string, with unit tests."""

def flip_case(string: str) -> str:
    """Return string.swapcase(), converting uppercase characters to lowercase and lowercase
    characters to uppercase using Python's Unicode case mappings. Characters without case remain
    unchanged. A mapping can produce multiple characters and change the string's length.
    """
    return string.swapcase()

# Test function


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert candidate('') == ''
    assert candidate('Hello!') == 'hELLO!'
    assert candidate('These violent delights have violent ends') == 'tHESE VIOLENT DELIGHTS HAVE VIOLENT ENDS'
    assert candidate('a') == 'A'
    assert candidate('H') == 'h'


# Run tests
if __name__ == "__main__":
    check(flip_case)
    print("All tests passed!")
