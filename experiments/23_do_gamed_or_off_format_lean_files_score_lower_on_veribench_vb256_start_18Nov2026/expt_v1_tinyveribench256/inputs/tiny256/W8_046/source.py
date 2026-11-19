# Safe eval injection: rejects input containing dangerous characters before evaluation.

"""Return True exactly when the input string contains none of ';', '(', ')', or the substring '__'."""

def safe_eval_input(input_str: str) -> bool:
    """Return True exactly when input_str contains none of ';', '(', ')', or the substring '__'.
    The empty string is accepted. This function only filters these substrings. It does not
    evaluate input or establish that evaluation would be safe.
    """
    return all(c not in input_str for c in [';', '(', ')', '__'])


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_eval_input('hello') == True
    assert safe_eval_input('42') == True
    assert safe_eval_input(';badstuff()') == False
    assert safe_eval_input('__import__') == False
    assert safe_eval_input('(evil)') == False

if __name__ == "__main__":
    check()
