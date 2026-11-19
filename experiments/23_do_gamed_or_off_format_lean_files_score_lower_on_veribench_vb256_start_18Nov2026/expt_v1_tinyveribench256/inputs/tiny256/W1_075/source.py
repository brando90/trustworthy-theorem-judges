# File: humaneval_12_longest.py
# HumanEval problem HumanEval/12

"""Longest string in a list (first one on ties, None if empty), with unit tests."""

from typing import List, Optional


def longest(strings: List[str]) -> Optional[str]:
    """ Out of list of strings, return the longest one. Return the first one in case of multiple
    strings of the same length. Return None in case the input list is empty.


    Used e.g. to pick the longest label when sizing a table column or to select the longest candidate among several suggested strings, with ties going to the first."""
    if not strings:
        return None

    maxlen = max(len(x) for x in strings)
    for s in strings:
        if len(s) == maxlen:
            return s

# Test function


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert candidate([]) == None
    assert candidate(['x', 'y', 'z']) == 'x'
    assert candidate(['x', 'yyy', 'zzzz', 'www', 'kkkk', 'abc']) == 'zzzz'
    assert candidate(['']) == ''
    assert candidate(['x']) == 'x'


# Run tests
if __name__ == "__main__":
    check(longest)
    print("All tests passed!")
