# File: humaneval_37_sort_even.py
# HumanEval problem HumanEval/37

"""Sort the entries at even indices of a list, leaving the odd indices in place, with unit tests."""

def sort_even(l: list):
    """This function takes a list l and returns a list l' such that
    l' is identical to l in the odd indicies, while its values at the even indicies are equal
    to the values of the even indicies of l, but sorted.

    Used e.g. to sort one channel of interleaved two-channel data such as alternating left and right samples while leaving the other channel unchanged."""
    evens = l[::2]
    odds = l[1::2]
    evens.sort()
    ans = []
    for e, o in zip(evens, odds):
        ans.extend([e, o])
    if len(evens) > len(odds):
        ans.append(evens[-1])
    return ans

# Test function


METADATA = {}


def check(candidate):
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert candidate([3, 7, 1, 9]) == [1, 7, 3, 9]
    assert candidate([1, 2, 3]) == [1, 2, 3]
    assert candidate([]) == []
    assert candidate([3]) == [3]
    assert candidate([9]) == [9]



# Run tests
if __name__ == "__main__":
    check(sort_even)
    print("All tests passed!")
