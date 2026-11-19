# File: humaneval_29_filter_by_prefix.py
# HumanEval problem HumanEval/29

"""Filter a list of strings to those starting with a given prefix, with unit tests."""

from typing import List


def filter_by_prefix(strings: List[str], prefix: str) -> List[str]:
    """ Filter an input list of strings only for ones that start with a given prefix.

    Used e.g. to select file names or commands that begin with a typed prefix for autocomplete or to filter log lines by a leading tag."""
    return [x for x in strings if x.startswith(prefix)]

# Test function


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert candidate([], 'john') == []
    assert candidate(['xxx', 'asd', 'xxy', 'john doe', 'xxxAAA', 'xxx'], 'xxx') == ['xxx', 'xxxAAA', 'xxx']
    assert candidate([], '') == []
    assert candidate(['xxx'], 'x') == ['xxx']
    assert candidate(['xxx', 'xxxAAA', 'john doe', 'xxy', 'asd', 'xxx'], 'xxx') == ['xxx', 'xxxAAA', 'xxx']


# Run tests
if __name__ == "__main__":
    check(filter_by_prefix)
    print("All tests passed!")
