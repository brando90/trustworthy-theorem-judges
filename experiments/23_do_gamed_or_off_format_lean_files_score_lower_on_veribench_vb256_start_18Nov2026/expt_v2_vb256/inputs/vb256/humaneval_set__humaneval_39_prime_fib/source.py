# File: humaneval_39_prime_fib.py
# HumanEval problem HumanEval/39

"""Search for the n-th prime Fibonacci number using trial division with floating-point square
roots, with unit tests. Zero returns 1. Square-root conversion can overflow.
"""

def prime_fib(n: int):
    """For positive n, search Fibonacci numbers in order and return the n-th one accepted by the
    local primality test, counting from one. Return 1 for zero. Negative n cannot reach a
    return. The test uses floating-point square roots and can raise OverflowError during the
    search.
    """
    import math

    def is_prime(p):
        """Return False for p below 2 or when a tested divisor divides p. Otherwise return True.
        Test integer divisors from 2 up to, but excluding, min(int(math.sqrt(p)) + 1, p - 1).
        The square-root calculation uses floating point and can raise OverflowError for large
        integers.
        """
        if p < 2:
            return False
        for k in range(2, min(int(math.sqrt(p)) + 1, p - 1)):
            if p % k == 0:
                return False
        return True
    f = [0, 1]
    while True:
        f.append(f[-1] + f[-2])
        if is_prime(f[-1]):
            n -= 1
        if n == 0:
            return f[-1]

# Test function


METADATA = {}


def check(candidate):
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert candidate(1) == 2
    assert candidate(2) == 3
    assert candidate(3) == 5
    assert candidate(4) == 13
    assert candidate(5) == 89



# Run tests
if __name__ == "__main__":
    check(prime_fib)
    print("All tests passed!")
