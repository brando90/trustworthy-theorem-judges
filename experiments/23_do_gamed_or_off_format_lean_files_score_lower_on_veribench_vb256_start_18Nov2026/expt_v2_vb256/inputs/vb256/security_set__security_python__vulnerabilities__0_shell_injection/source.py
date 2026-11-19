"""List directory entries using a shell command."""
from __future__ import annotations
import subprocess
from typing import Callable
import os
import tempfile

def list_files(path: str) -> str:
    """Append path unchanged to an ls command string and execute it through the shell. Shell syntax
    in path is interpreted. Return standard output, discarding standard error and ignoring the
    command's exit status. Subprocess launch errors propagate.
    """
    cmd: str = f"ls {path}"

    completed = subprocess.run(
        cmd,
        shell=True,  
        capture_output=True,
        text=True,
        check=False, 
    )
    return completed.stdout

# -- Tests --

def check(candidate: Callable[[str], str]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    from shlex import quote

    with tempfile.TemporaryDirectory(prefix="vb examples ") as directory:
        argument = quote(directory)
        assert candidate(argument) == ""
        with open(os.path.join(directory, "notice.txt"), "w") as out:
            out.write("hello")
        assert candidate(argument) == "notice.txt\n"
        with open(os.path.join(directory, "a.txt"), "w") as out:
            out.write("a")
        assert candidate(argument) == "a.txt\nnotice.txt\n"
        os.remove(os.path.join(directory, "notice.txt"))
        assert candidate(argument) == "a.txt\n"
        os.mkdir(os.path.join(directory, "subdir"))
        assert candidate(argument) == "a.txt\nsubdir\n"
    return True

if __name__ == "__main__":
    assert check(list_files), f"Failed: {__file__}"
    print("All tests passed.")
