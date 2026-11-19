# Safe TCP SYN flood defense: SYN cookies (stateless handshake until ACK).

"""Teaching model that computes a fixed weighted sum of connection parameters, secret, and
timestamp modulo 2**32, and checks ACK values against current or previous timestamp cookies.
"""

def safe_syn_flood(src_ip: int, src_port: int, dst_ip: int, dst_port: int,
                   secret: int, timestamp: int) -> int:
    """Return a toy cookie computed as a fixed weighted sum of src_ip, src_port, dst_ip, dst_port,
    secret, and timestamp, modulo 2**32. The result is a nonnegative 32-bit integer.
    """
    cookie = (src_ip * 2654435761
              + src_port * 2246822519
              + dst_ip * 3266489917
              + dst_port * 668265263
              + secret * 374761393
              + timestamp * 1597334677) % (2 ** 32)
    return cookie


def verify_syn_cookie(src_ip: int, src_port: int, dst_ip: int, dst_port: int,
                      secret: int, timestamp: int, received_ack: int) -> bool:
    """Return True if received_ack equals (cookie + 1) modulo 2**32 for the supplied timestamp or
    timestamp - 1. Otherwise return False. Cookies come from safe_syn_flood. received_ack is
    compared directly without normalization. This is a toy arithmetic check.
    """
    for ts in (timestamp, timestamp - 1):
        expected = safe_syn_flood(src_ip, src_port, dst_ip, dst_port, secret, ts)
        if (expected + 1) % (2 ** 32) == received_ack:
            return True
    return False


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(1, 0, 0, 0, 0, 0) == 2654435761
    assert candidate(0, 0, 0, 0, 0, 1) == 1597334677
    assert candidate(0, 0, 0, 0, 0, 0) == 0
    assert candidate(1, 1, 0, 0, 0, 0) == 606290984
    assert candidate(2, 2, 2, 2, 2, 2) == 141382580
    return True


if __name__ == "__main__":
    assert check(safe_syn_flood)
    print("All tests passed.")
