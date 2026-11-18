"""Append a new post only if the token is valid for username.

Teaching model for MIT 6.858.
"""

from typing import Callable, Dict, List, Optional, Tuple

# Represent a post as (creator: str, content: str)
Post = Tuple[str, str]


def safe_make_post(
    posts: List[Post],
    username: str,
    content: str,
    token: str,
    valid_tokens: Dict[str, str],
) -> Optional[List[Post]]:
    """Return a new list containing posts followed by (username, content) when
    valid_tokens.get(username) equals token. Otherwise return None. The supplied posts list is
    not modified.
    """
    # Fix: verify token before creating post
    if valid_tokens.get(username) != token:
        return None  # authentication failed — reject
    new_post = (username, content)
    return posts + [new_post]


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    tokens = {'alice': 'tok_alice', 'bob': 'tok_bob'}
    db: List[Post] = []
    result = candidate(db, 'alice', 'Hello world', 'tok_alice', tokens)
    assert result == [('alice', 'Hello world')]
    result2 = candidate(db, 'alice', 'Forged post', 'wrong_token', tokens)
    assert result2 is None
    result3 = candidate(db, 'alice', 'Forged', '', tokens)
    assert result3 is None
    result4 = candidate(db, 'alice', 'Forged', 'tok_bob', tokens)
    assert result4 is None
    result5 = candidate([], 'bob', "Bob's post", 'tok_bob', tokens)
    assert result5 == [('bob', "Bob's post")]
    return True


if __name__ == "__main__":
    assert check(safe_make_post), f"Failed: {__file__}"
    print("All tests passed.")
