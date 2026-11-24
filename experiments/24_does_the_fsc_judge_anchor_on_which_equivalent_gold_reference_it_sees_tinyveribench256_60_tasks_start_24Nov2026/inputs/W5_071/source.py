# Unsafe clickjacking frame check: allows framing regardless of ancestor count.

"""Returns True (allows framing) regardless of frame_ancestor_count."""

def unsafe_frame_check(frame_ancestor_count: int) -> bool:
    """Returns True (allows framing) regardless of frame_ancestor_count.

    MIT 6.858 Spring 2013 Quiz 1: web security / clickjacking.
    """
    return True


def check():
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert unsafe_frame_check(0) == True
    assert unsafe_frame_check(1) == True
    assert unsafe_frame_check(5) == True
    assert unsafe_frame_check(2) is True
    assert unsafe_frame_check(3) is True

if __name__ == "__main__":
    check()
