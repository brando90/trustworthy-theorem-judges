# File: humaneval_1_separate_paren_groups.py
# HumanEval problem HumanEval/1

"""Split a string of balanced parenthesis groups into its top-level groups, with unit tests."""

from typing import List


def separate_paren_groups(paren_string: str) -> List[str]:
    """For balanced input, return top-level parenthesis groups in order, ignoring all
    non-parenthesis characters. No balance validation is performed: append accumulated
    parentheses whenever a closing parenthesis returns the running depth to zero, and discard
    any remaining accumulation at the end. Return an empty list for empty input.
    """
    result = []
    current_string = []
    current_depth = 0

    for c in paren_string:
        if c == '(':
            current_depth += 1
            current_string.append(c)
        elif c == ')':
            current_depth -= 1
            current_string.append(c)

            if current_depth == 0:
                result.append(''.join(current_string))
                current_string.clear()

    return result

# Test function


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert candidate('(()()) ((())) () ((())()())') == ['(()())', '((()))', '()', '((())()())']
    assert candidate('() (()) ((())) (((())))') == ['()', '(())', '((()))', '(((())))']
    assert candidate('(()(())((())))') == ['(()(())((())))']
    assert candidate('( ) (( )) (( )( ))') == ['()', '(())', '(()())']
    assert candidate('') == []


# Run tests
if __name__ == "__main__":
    check(separate_paren_groups)
    print("All tests passed!")
