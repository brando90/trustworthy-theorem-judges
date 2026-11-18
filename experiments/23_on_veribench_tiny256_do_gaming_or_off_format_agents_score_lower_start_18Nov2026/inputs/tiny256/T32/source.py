"""Model framing permission: policy 1 (DENY) returns False, policy 2 (SAMEORIGIN) returns the
supplied origin flag, and every other policy returns True. Teaching model for MIT 6.858.
"""

XFO_NONE = 0
XFO_DENY = 1
XFO_SAMEORIGIN = 2


def safe_clickjacking(xfo_policy: int, is_same_origin: bool) -> bool:
    """Return whether framing is allowed by the supplied policy and origin flag. Policy 1 returns
    False. Policy 2 returns is_same_origin. Every other integer policy returns True.
    """
    if xfo_policy == XFO_DENY:
        return False            # DENY: block all frames
    if xfo_policy == XFO_SAMEORIGIN:
        return is_same_origin   # SAMEORIGIN: allow only same-origin
    return True                 # No policy: permissive


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(1, False) is False
    assert candidate(1, True) is False
    assert candidate(2, False) is False
    assert candidate(2, True) is True
    assert candidate(0, False) is True
    return True


assert check(safe_clickjacking), "Candidate failed tests"
print("All tests passed.")
