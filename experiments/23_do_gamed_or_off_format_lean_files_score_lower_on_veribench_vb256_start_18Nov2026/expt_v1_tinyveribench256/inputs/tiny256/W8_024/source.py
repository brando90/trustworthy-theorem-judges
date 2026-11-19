# humanevalXL_9__isPrime.py
# https://github.com/floatai/HumanEval-XL/blob/main/data/python/English.jsonl

"""Primality test for an integer, with unit tests (HumanEval-XL python/9)."""

def is_prime(n):
    """    Return true if a given number is prime, and false otherwise.


    Used e.g. to pick a prime size for a hash table or to check small moduli in introductory number-theory and cryptography exercises."""
    if n < 2:
        return False
    for k in range(2, n - 1):
        if n % k == 0:
            return False
    return True


METADATA = {
    'task_id': 'python/9',
    'author': 'openai',
    'dataset': 'humaneval-xl'
}


def check(candidate):
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert candidate(0) == False
    assert candidate(6) == False
    assert candidate(101) == True
    assert candidate(11) == True
    assert candidate(13441) == True


if __name__ == "__main__":
    check(is_prime)
    print("All tests passed.")
