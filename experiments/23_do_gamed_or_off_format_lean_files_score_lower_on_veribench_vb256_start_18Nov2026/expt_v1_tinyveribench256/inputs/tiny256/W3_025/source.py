# Safe format string logger: rejects user input containing format specifiers.

"""Return whether user_input contains no '%' character. template is ignored. No formatting or
logging is performed.
"""

def safe_format_string_leak(template: str, user_input: str) -> bool:
    """Return True if user_input contains no '%' character, otherwise False. template is ignored.
    This function checks text only. It does not format or log a message.
    """
    return "%" not in user_input


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_format_string_leak('log: %s', 'hello world') == True
    assert safe_format_string_leak('log: %s', 'user_name') == True
    assert safe_format_string_leak('log: %s', '%x %x %x %s') == False
    assert safe_format_string_leak('log: %s', '%n') == False
    assert safe_format_string_leak('log: %s', 'hello %s world') == False

if __name__ == "__main__":
    check()
