# Unsafe open redirect: allows redirect to any URL without validating the allowed host.

"""Returns True (allows redirect) regardless of whether redirect_url contains allowed_host."""

def unsafe_redirect(redirect_url: str, allowed_host: str) -> bool:
    """Returns True (allows redirect) regardless of whether redirect_url contains allowed_host.

    MIT 6.858 Quiz 1, Spring 2015: Open redirect vulnerability.
    """
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_redirect('https://bank.com/dashboard', 'bank.com') == True
    assert unsafe_redirect('https://evil.com/phish', 'bank.com') == True
    assert unsafe_redirect('http://bank.com/page', 'bank.com') == True
    assert unsafe_redirect('', 'bank.com') == True
    assert unsafe_redirect('', '') is True

if __name__ == "__main__":
    check()
