# -*- coding: utf-8 -*-
"""Run a command selected from a small menu."""
from __future__ import annotations

import os
import subprocess
import tempfile
import shlex
from typing import Callable, Dict, List


def execute_command_safe(cmd_name: str, args: str = "") -> str:
    """Map list, count, and search to ls --, wc -l --, and grep -r --. Append shlex.split arguments
    and execute without a shell. Return standard output. Return error strings for unknown names,
    malformed quoting, nonzero exits, or missing executables. Other execution exceptions
    propagate.
    """
    command_map: Dict[str, List[str]] = {
        "list": ["ls", "--"],
        "count": ["wc", "-l", "--"], 
        "search": ["grep", "-r", "--"]
    }
    
    if cmd_name not in command_map:
        return "Error: Unknown command"
    
    base_argv: List[str] = command_map[cmd_name].copy()
    
    try:
        if args.strip():
            user_args: List[str] = shlex.split(args)
            base_argv.extend(user_args)
            
    except ValueError as e:
        return f"Error: Invalid arguments - {e}"

    try:
        completed = subprocess.run(
            base_argv,
            shell=False,
            capture_output=True,
            text=True,
            check=True,
        )
        return completed.stdout
    except subprocess.CalledProcessError as e:
        return f"Error: {e.stderr.strip() if e.stderr else 'Command failed'}"
    except FileNotFoundError:
        return f"Error: Command not found"


# -- Tests --

def check(candidate: Callable[[str, str], str]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    from shlex import quote

    with tempfile.TemporaryDirectory(prefix="vb examples ") as directory:
        argument = quote(directory)
        assert candidate("list", argument) == ""
        with open(os.path.join(directory, "notice.txt"), "w") as out:
            out.write("hello")
        assert candidate("list", argument) == "notice.txt\n"
        with open(os.path.join(directory, "a.txt"), "w") as out:
            out.write("a")
        assert candidate("list", argument) == "a.txt\nnotice.txt\n"
        assert candidate("missing", argument) == "Error: Unknown command"
        os.mkdir(os.path.join(directory, "subdir"))
        assert candidate("list", argument) == "a.txt\nnotice.txt\nsubdir\n"
    return True


if __name__ == "__main__":
    assert check(execute_command_safe)
    print("All tests passed.")
