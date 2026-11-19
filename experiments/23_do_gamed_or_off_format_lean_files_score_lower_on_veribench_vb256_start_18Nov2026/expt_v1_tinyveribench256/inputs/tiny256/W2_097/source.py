# Safe OAuth redirect check: validates redirect_url against the client's allowed URL list.

"""Returns True only when redirect_url appears in the allowed_urls list."""

def safe_oauth_redirect(redirect_url: str, client_id: str, allowed_urls: list) -> bool:
    """Return whether redirect_url is a member of allowed_urls. client_id is ignored. The function
    does not verify that the supplied list belongs to that client.
    """
    return redirect_url in allowed_urls


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_oauth_redirect('https://rp1.example.com/cb', 'rp1', ['https://rp1.example.com/cb', 'https://rp2.example.com/cb']) == True
    assert safe_oauth_redirect('https://rp2.example.com/cb', 'rp2', ['https://rp1.example.com/cb', 'https://rp2.example.com/cb']) == True
    assert safe_oauth_redirect('https://evil.com/steal', 'rp1', ['https://rp1.example.com/cb', 'https://rp2.example.com/cb']) == False
    assert safe_oauth_redirect('https://rp3.com/cb', 'rp1', ['https://rp1.example.com/cb', 'https://rp2.example.com/cb']) == False
    assert safe_oauth_redirect('', 'rp1', ['https://rp1.example.com/cb', 'https://rp2.example.com/cb']) == False

if __name__ == "__main__":
    check()
