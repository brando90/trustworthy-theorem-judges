"""Return a new list containing the existing posts followed by (username, content). Leave the
supplied list unchanged and ignore the token.
"""

from typing import List, Tuple


# Represent a post as (creator: str, content: str)
Post = Tuple[str, str]


def unsafe_make_post(
    posts: List[Post],
    username: str,
    content: str,
    _token: str,
) -> List[Post]:
    """Return a new list containing posts followed by (username, content), without modifying posts.
    Ignore _token. No authentication or username validation is performed.
    """
    # Vulnerability: token is ignored — no authentication
    new_post = (username, content)
    return posts + [new_post]


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    db: List[Post] = []
    db = candidate(db, 'alice', 'Hello world', 'valid_token_alice')
    assert db == [('alice', 'Hello world')]
    db2: List[Post] = []
    db2 = candidate(db2, 'bob', 'Impersonated!', '')
    assert db2 == [('bob', 'Impersonated!')]
    assert candidate([], '', '', '') == [('', '')]
    assert candidate([('amy', 'a')], 'bo', 'b', 't') == [('amy', 'a'), ('bo', 'b')]
    assert candidate([], 'sam', 'notes', 'x') == [('sam', 'notes')]
    return True


assert check(unsafe_make_post), "Candidate failed post authority tests"
print("All tests passed.")
