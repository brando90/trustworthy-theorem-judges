# Synthetic VeriBench task — Inspired by: token bucket with decay-based token drain
# Original language: Python
# Category: 14_critical_infra
"""Computes a token count: return capacity if tokens + refill exceeds capacity. Otherwise subtract
decay_rate only when tokens > decay_rate, then add refill.
"""

from typing import Callable


def pre_condition(tokens: int, refill: int, capacity: int, decay_rate: int) -> bool:
    """Decay rate must be non-negative."""
    return decay_rate >= 0


def my_token_bucket_decay(tokens: int, refill: int, capacity: int, decay_rate: int) -> int:
    """Return capacity when adding refill overflows the bucket. Otherwise add refill, subtracting
    decay_rate first only when tokens exceeds that rate.

    Raise AssertionError when pre_condition rejects the arguments.
    """
    assert pre_condition(tokens, refill, capacity, decay_rate), "pre violated"
    if tokens + refill > capacity:
        return capacity
    elif tokens > decay_rate:
        return tokens - decay_rate + refill
    else:
        return tokens + refill


def check(candidate: Callable[[int, int, int, int], int]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(8, 5, 10, 2) == 10
    assert candidate(5, 3, 10, 2) == 6
    assert candidate(1, 3, 10, 2) == 4
    assert candidate(10, 0, 10, 3) == 7
    assert candidate(0, 5, 10, 2) == 5
    return True


if __name__ == "__main__":
    assert check(my_token_bucket_decay)
    print(f"All tests passed: {__file__}!")
