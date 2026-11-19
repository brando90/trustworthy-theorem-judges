# Synthetic VeriBench task — Inspired by: VM entry gate with pending-IRQ, PC match, guest range
# Original language: Python
# Category: 11_hypervisor
# Lines: generated
"""Compute a toy entry predicate: pending_irq must be falsy, saved_pc must equal resume_pc, and
guest_id must be less than max_guests. No lower bound on guest_id is checked.
"""

from typing import Callable


def pre_condition(pending_irq: bool, saved_pc: int, resume_pc: int, guest_id: int, max_guests: int) -> bool:
    """Return whether max_guests is an instance of int greater than zero; True qualifies. Ignore
    all other arguments.
    """
    return isinstance(max_guests, int) and max_guests > 0


def my_vm_exit_cond_restore(pending_irq: bool, saved_pc: int, resume_pc: int, guest_id: int, max_guests: int) -> bool:
    """Return the short-circuit conjunction of not pending_irq, saved_pc == resume_pc, and guest_id
    < max_guests. Negative guest IDs are not rejected. Raise AssertionError unless max_guests is
    an int greater than zero. Other arguments are unchecked. Evaluated comparisons may raise
    TypeError.
    """
    assert pre_condition(pending_irq, saved_pc, resume_pc, guest_id, max_guests), 'pre violated'
    return (not pending_irq) and (saved_pc == resume_pc) and (guest_id < max_guests)


def check(candidate: Callable) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(False, 100, 100, 0, 4) == True
    assert candidate(False, 100, 100, 3, 4) == True
    assert candidate(True, 100, 100, 0, 4) == False
    assert candidate(False, 100, 101, 0, 4) == False
    try:
        candidate(False, 0, 0, 0, 0)
    except AssertionError:
        pass
    else:
        raise AssertionError('expected AssertionError')
    return True


if __name__ == '__main__':
    assert check(my_vm_exit_cond_restore)
    print(f'All tests passed: {__file__}!')
