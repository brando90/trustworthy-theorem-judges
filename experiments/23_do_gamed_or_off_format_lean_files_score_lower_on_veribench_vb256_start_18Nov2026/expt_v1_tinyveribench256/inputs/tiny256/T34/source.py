"""Return the terminal node's value by following next links. Raise ValueError for an empty list.
Traversal does not terminate if the reachable links contain a cycle.
"""

from typing import Optional, Callable


class Node:
    """A singly linked list node holding an integer value and a link to the next node."""
    def __init__(self, value: int, next_node: Optional['Node']=None):
        """Create a node with the given value and next link."""
        self.value = value
        self.next = next_node


def safe_find_last(node: Optional[Node]) -> int:
    """Follow next links and return the value of the node whose next is None. Raise
    ValueError("empty list") if node is None. A reachable cycle causes traversal to continue
    indefinitely.
    """
    if node is None:
        raise ValueError("empty list")
    current = node
    while current.next is not None:
        current = current.next
    return current.value


def check(candidate: Callable[[Optional[Node]], int]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(Node(1, Node(2, Node(3)))) == 3
    assert candidate(Node(42)) == 42
    try:
        candidate(None)
    except ValueError:
        pass
    else:
        raise AssertionError("expected ValueError")
    assert candidate(Node(-3, Node(0))) == 0
    assert candidate(Node(2, Node(-5))) == -5
    return True


if __name__ == "__main__":
    assert check(safe_find_last), f"Failed: {__file__}"
    print("All tests passed.")

