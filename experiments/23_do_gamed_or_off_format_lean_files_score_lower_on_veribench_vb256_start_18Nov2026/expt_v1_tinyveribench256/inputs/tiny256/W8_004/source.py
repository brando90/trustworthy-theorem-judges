# File: humaneval_18_how_many_times.py
# HumanEval problem HumanEval/18

"""Count of overlapping occurrences of a substring in a string, with unit tests."""

def how_many_times(string: str, substring: str) -> int:
    """Return the number of matching substring positions in string, including overlapping matches.
    An empty substring matches len(string) + 1 positions. Return zero when substring is longer
    than string.
    """
    times = 0

    for i in range(len(string) - len(substring) + 1):
        if string[i:i+len(substring)] == substring:
            times += 1

    return times

# Test function


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert candidate('', 'x') == 0
    assert candidate('xyxyxyx', 'x') == 4
    assert candidate('cacacacac', 'cac') == 4
    assert candidate('john doe', 'john') == 1
    assert candidate('', '') == 1


# Run tests
if __name__ == "__main__":
    check(how_many_times)
    print("All tests passed!")
