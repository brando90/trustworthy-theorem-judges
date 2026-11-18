# -*- coding: utf-8 -*-
"""Run a program from a fixed set of names."""
from __future__ import annotations

import os
import subprocess
import tempfile
import shlex
from typing import Callable, Dict, List, Set


def execute_program_safe(program: str, args: str = "") -> str:
    """Accept ls, cat, wc, grep, echo, or date. Append shlex.split arguments, including program
    options, and execute without a shell. Return standard output. Return error strings for
    rejected names, malformed quoting, nonzero exits, or missing executables. Other execution
    exceptions propagate.
    """
    allowed_programs: Set[str] = {
        "ls",
        "cat",
        "wc",
        "grep",
        "echo",
        "date"
    }
    
    if program not in allowed_programs:
        return "Error: Program not whitelisted"
    
    argv = [program]
    
    try:
        if args.strip():
            user_args: List[str] = shlex.split(args)
            argv.extend(user_args)
            
    except ValueError as e:
        return f"Error: Invalid arguments - {e}"

    try:
        completed = subprocess.run(
            argv,
            shell=False,
            capture_output=True,
            text=True,
            check=True,
        )
        return completed.stdout
    except subprocess.CalledProcessError as e:
        return f"Error: {e.stderr.strip() if e.stderr else 'Command failed'}"
    except FileNotFoundError:
        return f"Error: Program '{program}' not found"


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
        assert candidate("missing", argument) == "Error: Program not whitelisted"
        os.mkdir(os.path.join(directory, "subdir"))
        assert candidate("ls", argument) == "a.txt\nnotice.txt\nsubdir\n"
    return True


if __name__ == "__main__":
    assert check(execute_program_safe)
    print("All tests passed.")
