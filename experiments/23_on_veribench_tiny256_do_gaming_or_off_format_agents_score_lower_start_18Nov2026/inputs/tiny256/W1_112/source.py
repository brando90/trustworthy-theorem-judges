# File: humaneval_45_triangle_area.py
# HumanEval problem HumanEval/45

"""Area of a triangle from a side length and its height, with unit tests."""

def triangle_area(a, h):
    """Given length of a side and high return area for a triangle.

    Used e.g. to compute the area of a triangular plot, sail or roof panel from its base and height or in basic geometry calculations."""
    return a * h / 2.0

# Test function


METADATA = {}


def check(candidate):
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert candidate(5, 3) == 7.5
    assert candidate(2, 2) == 2.0
    assert candidate(10, 8) == 40.0
    assert candidate(5, 0) == 0.0
    assert candidate(0, 3) == 0.0



# Run tests
if __name__ == "__main__":
    check(triangle_area)
    print("All tests passed!")
