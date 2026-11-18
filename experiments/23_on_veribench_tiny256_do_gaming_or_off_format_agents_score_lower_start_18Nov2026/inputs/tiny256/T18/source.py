# Unsafe OAuth redirect check: does not validate the redirect URL against allowed patterns.

"""Approve the request without checking whether redirect_url is in the allowed set for client_id."""

def unsafe_oauth_redirect(redirect_url: str, client_id: str, allowed_urls: list) -> bool:
    """Approve the request without checking whether redirect_url is in the allowed set for
    client_id.

    MIT 6.858 Fall 2012 Quiz 2: OAuth redirect URL not validated (Ben's modified protocol).
    """
    return True  # vulnerable: redirect never validated


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_oauth_redirect('https://rp1.example.com/cb', 'rp1', ['https://rp1.example.com/cb', 'https://rp2.example.com/cb']) == True
    assert unsafe_oauth_redirect('https://evil.com/steal', 'rp1', ['https://rp1.example.com/cb', 'https://rp2.example.com/cb']) == True
    assert unsafe_oauth_redirect('https://rp3.com/cb', 'rp1', ['https://rp1.example.com/cb', 'https://rp2.example.com/cb']) == True
    assert unsafe_oauth_redirect('', 'rp1', ['https://rp1.example.com/cb', 'https://rp2.example.com/cb']) == True
    assert unsafe_oauth_redirect('', '', []) is True

if __name__ == "__main__":
    check()
