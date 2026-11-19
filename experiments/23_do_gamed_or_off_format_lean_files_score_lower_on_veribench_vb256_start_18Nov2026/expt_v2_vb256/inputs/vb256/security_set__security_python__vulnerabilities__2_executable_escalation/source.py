"""Execute a user-selected shell command."""
from __future__ import annotations
import subprocess
from typing import Callable
import os
import tempfile

def execute_program(program: str, args: str = "") -> str:
    """Build a shell command from the program and raw argument string, without quoting or
    whitelisting them, and return standard output. The wrapper discards standard error and
    ignores the exit status.
    """
    full_cmd = f"{program} {args}" if args.strip() else program

    completed = subprocess.run(
        full_cmd,
        shell=True,  
        capture_output=True,
        text=True,
        check=False, 
    )
    return completed.stdout

# -- Tests --

def check(candidate: Callable[[str, str], str]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    from shlex import quote

    with tempfile.TemporaryDirectory(prefix="vb examples ") as directory:
        argument = quote(directory)
        assert candidate("ls", argument) == ""
        with open(os.path.join(directory, "notice.txt"), "w") as out:
            out.write("hello")
        assert candidate("ls", argument) == "notice.txt\n"
        with open(os.path.join(directory, "a.txt"), "w") as out:
            out.write("a")
        assert candidate("ls", argument) == "a.txt\nnotice.txt\n"
        assert candidate("echo", "hello") == "hello\n"
        os.mkdir(os.path.join(directory, "subdir"))
        assert candidate("ls", argument) == "a.txt\nnotice.txt\nsubdir\n"
    return True

if __name__ == "__main__":
    assert check(execute_program), f"Failed: {__file__}"
    print("All tests passed.")
