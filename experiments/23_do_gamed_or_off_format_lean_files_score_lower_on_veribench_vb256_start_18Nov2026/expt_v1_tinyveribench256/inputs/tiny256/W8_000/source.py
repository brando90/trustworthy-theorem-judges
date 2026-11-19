# File: humaneval_17_parse_music.py
# HumanEval problem HumanEval/17

"""Parser from an ASCII music string to a list of note durations in beats, with unit tests."""

from typing import List


def parse_music(music_string: str) -> List[int]:
    """Split music_string on literal spaces, ignoring empty tokens. Return durations in order: 'o'
    means four beats, 'o|' two beats, and '.|' one beat. Return an empty list for empty or
    space-only input. Raise KeyError for any other token.
    """
    note_map = {'o': 4, 'o|': 2, '.|': 1}
    return [note_map[x] for x in music_string.split(' ') if x]


# Test function

def check(candidate):
    """Run the fixed examples. A mismatched observation raises AssertionError."""
    assert candidate('') == []
    assert candidate('o o o o') == [4, 4, 4, 4]
    assert candidate('.| .| .| .|') == [1, 1, 1, 1]
    assert candidate('o| o| .| .| o o o o') == [2, 2, 1, 1, 4, 4, 4, 4]
    assert candidate('o| .| o| .| o o| o o|') == [2, 1, 2, 1, 4, 2, 4, 2]


# Run tests
if __name__ == "__main__":
    check(parse_music)
    print("All tests passed!")
