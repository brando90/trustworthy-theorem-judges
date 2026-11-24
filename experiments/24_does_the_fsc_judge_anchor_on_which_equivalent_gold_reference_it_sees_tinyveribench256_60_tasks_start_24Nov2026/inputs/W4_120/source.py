# Unsafe TCP RST handling: accepts RST if sequence number is inside the receive window.

"""Model a reset acceptance decision: return whether rcv_nxt <= pkt_seq < rcv_nxt + rcv_wnd using
ordinary integer arithmetic, without sequence-number wraparound.
"""

def unsafe_tcp_reset(
    pkt_seq: int,
    rcv_nxt: int,
    rcv_wnd: int,
) -> bool:
    """Return whether rcv_nxt <= pkt_seq < rcv_nxt + rcv_wnd using ordinary integer arithmetic
    without sequence-number wraparound. A zero or negative rcv_wnd returns False. This function
    only returns a Boolean decision.
    """
    # Vulnerable condition: accept RST if sequence is anywhere within receive window.
    return rcv_nxt <= pkt_seq < rcv_nxt + rcv_wnd


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(1000, 1000, 65535) == True
    assert candidate(33000, 1000, 65535) == True
    assert candidate(66534, 1000, 65535) == True
    assert candidate(999, 1000, 65535) == False
    assert candidate(1000, 1000, 0) == False
    return True


if __name__ == "__main__":
    assert check(unsafe_tcp_reset), f"Failed: {__file__}"
