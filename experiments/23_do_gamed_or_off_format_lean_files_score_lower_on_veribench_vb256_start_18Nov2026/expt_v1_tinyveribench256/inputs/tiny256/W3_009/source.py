# Safe redirect: allows redirect only when URL starts with 'https://' + allowed_host.

"""Returns True only when redirect_url starts with 'https://' + allowed_host."""

def safe_redirect(redirect_url: str, allowed_host: str) -> bool:
    """Returns True only when redirect_url starts with 'https://' + allowed_host.

    MIT 6.858 Quiz 1, Spring 2015: Open redirect fix.
    """
    return redirect_url.startswith("https://" + allowed_host)


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert safe_redirect('https://bank.com/dashboard', 'bank.com') == True
    assert safe_redirect('https://bank.com/', 'bank.com') == True
    assert safe_redirect('https://evil.com/phish', 'bank.com') == False
    assert safe_redirect('http://bank.com/page', 'bank.com') == False
    assert safe_redirect('', 'bank.com') == False

if __name__ == "__main__":
    check()
