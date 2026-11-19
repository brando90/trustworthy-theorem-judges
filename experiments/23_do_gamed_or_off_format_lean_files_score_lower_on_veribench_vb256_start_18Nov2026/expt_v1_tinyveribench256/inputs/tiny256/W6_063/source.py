"""Follow next links to return the terminal node's value. Passing None raises AttributeError. A
cycle of Nodes prevents termination.
"""

class Node:
    """Singly linked list node holding an int value and an optional next node."""
    def __init__(self, value: int, next_node=None):
        """Build a node with the given value and next node."""
        self.value = value
        self.next = next_node

def unsafe_find_last(node: Node) -> int:
    """Follow next links until a node's next is None, then return that node's value. Passing None
    raises AttributeError. A cycle of Nodes prevents termination.
    """
    current = node
    while current.next is not None:
        current = current.next
    return current.value


def check(candidate) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    n3 = Node(3, None)
    n2 = Node(2, n3)
    n1 = Node(1, n2)
    assert candidate(n1) == 3
    single = Node(42, None)
    assert candidate(single) == 42
    lonely = Node(99, None)
    assert candidate(lonely) == 99
    assert candidate(Node(-3, Node(0))) == 0
    assert candidate(Node(2, Node(-5))) == -5
    return True


assert check(unsafe_find_last), "Candidate failed null pointer tests"
print("All tests passed.")
