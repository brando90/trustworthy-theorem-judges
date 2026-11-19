# File: humaneval_15_string_sequence.py
# HumanEval problem HumanEval/15

"""Space-delimited string of the integers 0 through n, with unit tests."""

def string_sequence(n: int) -> str:
    """Return decimal integers from 0 through n inclusive, separated by single spaces without
    leading or trailing spaces. Return an empty string when n is negative.
    """
    return ' '.join([str(x) for x in range(n + 1)])

# Test function


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert candidate(0) == '0'
    assert candidate(3) == '0 1 2 3'
    assert candidate(10) == '0 1 2 3 4 5 6 7 8 9 10'
    assert candidate(-1) == ''
    assert candidate(1) == '0 1'


# Run tests
if __name__ == "__main__":
    check(string_sequence)
    print("All tests passed!")
