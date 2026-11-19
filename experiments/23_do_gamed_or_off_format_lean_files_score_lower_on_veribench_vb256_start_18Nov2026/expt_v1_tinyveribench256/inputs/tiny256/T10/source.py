# Safe SQL taint check: rejects query execution when user-supplied data reaches the SQL sink.

"""Provide a toy SQL taint guard returning True when both is_user_supplied and
passed_through_wrapper are false. Query contents are not inspected.
"""

def safe_sql_taint(query: str, is_user_supplied: bool, passed_through_wrapper: bool) -> bool:
    """Return True when both is_user_supplied and passed_through_wrapper are false, otherwise
    False. query is ignored. These supplied flags determine the result. The function does not
    analyze SQL or establish that execution is safe.
    """
    tainted = is_user_supplied or passed_through_wrapper
    return not tainted


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_sql_taint('SELECT * FROM users WHERE id=1', False, False) == True
    assert safe_sql_taint('SELECT 1', False, False) == True
    assert safe_sql_taint('SELECT * FROM users WHERE id=$_GET[id]', True, False) == False
    assert safe_sql_taint('SELECT * FROM users WHERE id=$x', True, True) == False
    assert safe_sql_taint('SELECT 1', False, True) == False

if __name__ == "__main__":
    check()
