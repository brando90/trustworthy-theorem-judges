#!/usr/bin/env python3
"""Generate Harbor task directories for VeriBench Python-to-Lean tasks."""

import argparse
import importlib.util
import os
import re
import shutil
from pathlib import Path

# ---- Paths ----
VERIBENCH_ROOT = Path(os.environ.get("VERIBENCH_ROOT", Path(__file__).resolve().parents[2])).resolve()
PY_SRC = VERIBENCH_ROOT / "veribench_dataset" / "py_src"
LEAN_SRC = VERIBENCH_ROOT / "veribench_dataset" / "lean_src" / "veribench"
SETUP_SCRIPT = VERIBENCH_ROOT / "veribench_setup.sh"
JUDGE_PROMPT = (
    VERIBENCH_ROOT / "py_src" / "veribench_prompts"
    / "judge_prompts" / "file_equiv_prompts" / "claude_code_judge_prompt.txt"
)
# Agent-facing spec version. v2 = 2026-08 proof-policy fix (expt 70/72): agents are told
# to PROVE what they state; `sorry` is a legal last resort worth zero IC_proofs credit.
# v3 was an unmerged numeric-layer draft whose scoring promise was not implemented.
# v4 = 2026-09 numeric modelling guidance, without accepted-layer scoring guarantees.
# v5 = 2026-09-14 property-based tests (PBTs) required for every stated property (Brando);
#      no SCSC factor checks PBT presence yet.
# Preserve archived v2/v3 packs and record the exact prompt stamp for new runs.
# Validators must accept "agent-spec v<N>" for N >= 2, never one literal version, so that
# archival packs keep validating while the current pack gate keeps its meaning.
# v6 = 2026-09-20 explicit completion of every assigned task/file/question within declared bounds.
# v7 = 2026-09-29 the Proof Policy states the kernel-axiom rule the canonical scorer enforces: `native_decide`,
#      new axioms and dependence on a `sorry`/`native_decide` helper earn zero, as `sorry` and `admit` already did
#      (Brando: every proof must be attempted, so a zero means the agent could not prove it).
# v8 = 2026-10-09 the namespace hint is valid Lean. Since this adapter was added (2026-03-12, 21c3f9340a) every pack
#      suggested `namespace {lean_stem}`, and 533/896 stems begin with a digit (e.g. `10_MyEvenSumParity`), which
#      Lean 4 rejects. Those 533 tasks now show the name quoted, `namespace «10_MyEvenSumParity»` ...
#      `end «10_MyEvenSumParity»`; the other 363 instructions are byte-identical to v7 apart from this stamp.
#      Evidence: experiments/ideas/rl4cv_factored_scsc_results_implications_for_vb/namespace_defect_v8/.
AGENT_SPEC_VERSION = "VeriBench agent-spec v8 (2026-10-09 valid Lean namespace hint)"

# Keep direct-file imports working for existing offline pack generators.
_completion_spec = importlib.util.spec_from_file_location(
    "veribench_completion_contract", Path(__file__).with_name("completion_contract.py"))
_completion = importlib.util.module_from_spec(_completion_spec)
_completion_spec.loader.exec_module(_completion)

TEMPLATE_DIR = Path(__file__).parent / "template"
OUTPUT_DIR = Path(__file__).parent.parent / "tasks"


def find_py_files() -> list[Path]:
    """Walk py_src/ recursively to find all .py files, sorted."""
    py_files = []
    for root, _dirs, files in os.walk(PY_SRC):
        for f in sorted(files):
            if f.endswith(".py"):
                py_files.append(Path(root) / f)
    return sorted(py_files)


def py_to_lean_path(py_path: Path) -> Path:
    """Map a Python source to its gold Lean reference.

    py_src/easy_set/1_MyAdd.py → lean_src/veribench/easy_set/1_MyAdd.lean
    """
    rel = py_path.relative_to(PY_SRC)
    exact_path = LEAN_SRC / rel.with_suffix(".lean")
    if exact_path.exists():
        return exact_path

    # The industry expansion stores Python files as snake_case and Lean files as
    # PascalCase, e.g. my_fprime_crc_match.py -> MyFprimeCrcMatch.lean.
    lean_dir = LEAN_SRC / rel.parent
    normalized_py_stem = re.sub(r"[^a-z0-9]+", "", py_path.stem.lower())
    for candidate in sorted(lean_dir.glob("*.lean")):
        normalized_lean_stem = re.sub(r"[^a-z0-9]+", "", candidate.stem.lower())
        if normalized_lean_stem == normalized_py_stem:
            return candidate

    return exact_path


def make_task_id(py_path: Path) -> str:
    """Create a task ID from the Python file's relative path.

    easy_set/1_MyAdd.py → easy_set__1_MyAdd
    security_set/security_6858/safe/0_unsafeCopy_safe.py → security_set__security_6858__safe__0_unsafeCopy_safe
    """
    rel = py_path.relative_to(PY_SRC)
    # Lowercase: Docker image names must be lowercase
    return str(rel.with_suffix("")).replace(os.sep, "__").lower()


def extract_canary(gold_content: str) -> str:
    """Extract a canary string from the gold Lean file.

    Uses the namespace name, which is unique per file and unlikely to appear
    in a from-scratch solution.
    """
    ns_match = re.search(r"^namespace\s+(\w+)", gold_content, re.MULTILINE)
    if ns_match:
        return ns_match.group(1)
    # Fallback: first theorem name
    thm_match = re.search(r"^theorem\s+(\w+)", gold_content, re.MULTILINE)
    if thm_match:
        return thm_match.group(1)
    return "veribench_gold"


def extract_split(py_path: Path) -> str:
    """Extract the top-level split (easy_set, cs_set, etc.)."""
    return py_path.relative_to(PY_SRC).parts[0]


_PLAIN_LEAN_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
# Command keywords that cannot be used bare as a namespace name.
_LEAN_KEYWORDS = frozenset({
    "abbrev", "axiom", "by", "class", "def", "deriving", "do", "else", "end", "example", "export", "fun", "if",
    "import", "in", "inductive", "instance", "lemma", "let", "match", "mutual", "namespace", "noncomputable", "open",
    "partial", "private", "protected", "section", "structure", "then", "theorem", "universe", "variable", "where",
    "with"})


def lean_namespace(lean_stem: str) -> str:
    """The namespace name the instruction shows: the stem itself when it is a plain Lean identifier, else the stem
    in «» quotes. Lean 4 rejects `namespace 10_MyEvenSumParity` (an identifier cannot begin with a digit) and
    accepts `namespace «10_MyEvenSumParity»`."""
    if _PLAIN_LEAN_IDENT.fullmatch(lean_stem) and lean_stem not in _LEAN_KEYWORDS:
        return lean_stem
    if not lean_stem or any(c in lean_stem for c in "«»\r\n"):
        raise ValueError(f"cannot write Lean stem {lean_stem!r} as a namespace name")
    return f"«{lean_stem}»"


def generate_instruction(py_content: str, lean_stem: str) -> str:
    """Generate instruction.md content for one task."""
    namespace = lean_namespace(lean_stem)
    if namespace == lean_stem:  # byte-identical to agent-spec v7 for these tasks
        namespace_item = f"3. Namespace (e.g., `namespace {namespace}`)"
        end_item = "14. `end` namespace"
    else:
        namespace_item = (f"3. Namespace (e.g., `namespace {namespace}`) -- the file name begins with a digit and a "
                          "Lean identifier cannot, so keep the `«»` quotes wherever this name appears")
        end_item = f"14. `end {namespace}` (closes the namespace; keep the `«»` quotes)"
    instruction = f"""<!-- {AGENT_SPEC_VERSION} -->
# Task: Translate Python to Lean 4

Translate the following Python program into a Lean 4 formalization.

## Python Source Code

```python
{py_content}```

## Output Requirements

Write your Lean 4 formalization to:

```
/home/user/lean_project/Veribench/{lean_stem}.lean
```

## VeriBench File Format

Your Lean 4 file must follow this structure (in order):
1. `import Mathlib` at the top
2. Module docstring describing the file
{namespace_item}
4. Implementation (functional definition)
5. Unit tests using `example : ... := by native_decide` and `#eval`
6. Pre-condition predicate (`def Pre`)
7. Property propositions (`def <name>_prop`) and theorems (`theorem <name>_thm ...`) -- prove each theorem
8. Post-condition (`def Post_prop`) as conjunction of properties
9. Property-based tests (required) -- see "Property-Based Tests" below
10. Correctness theorem: `Pre -> Post` -- prove it
11. Imperative implementation using `Id.run do` with mutable state
12. Imperative tests
13. Equivalence theorem: functional = imperative -- prove it
{end_item}

## Property-Based Tests (required)

- Unit tests check fixed examples. Property-based tests (PBTs) check a property on many inputs. Write at least one PBT for every executable property you state (each `_prop`, and the post-condition), placed after the post-condition definition. A PBT states the property's executable Boolean form over the implementation; it does not need a `Decidable` instance for your `Prop` definitions.
- Randomized PBT: `#eval Plausible.Testable.check (∀ a b : Nat, myAdd a b = myAdd b a)`. Plausible ships with Mathlib; the file fails to compile if it finds a counterexample. Restrict to admissible inputs with a decidable implication, e.g. `(∀ xs : List Nat, 0 < xs.length → ...)`; a "Gave up" warning means few samples met the precondition, so add a bounded PBT for that property.
- Bounded PBT, for input types without a Plausible sampler or when you want exhaustive small cases: `example : (List.range 30).all (fun n => myF n ≥ 0) = true := by native_decide`.
- Executable means the check reduces to computable operations (`Nat`, `Int`, `Bool`, `String`, `List`, `Array`, `Float`, ...). A property stated over `Real` or another noncomputable type has no executable check (`Real` comparisons are not computable). For such a property, test its executable counterpart where one exists (for example the `Float` or `Rat` implementation layer on concrete inputs) and add a comment naming the untested `Real` property; if no executable counterpart exists, add a comment `-- PBT: not executable (<reason>)`. Keep the original theorem, its type and its input domain unchanged: never restate, narrow or weaken a property to make it testable.
- Never use the `plausible` tactic to close a theorem or `example`: when it finds no counterexample it admits the goal, exactly like `sorry`.
- A passing PBT is evidence, not a proof: still state and prove every theorem. A PBT that fails is telling you the property or the implementation is wrong -- fix whichever one misrepresents the Python program, never by weakening the property.

## Numeric Modelling Guidance (read before you state theorems)

- Python `float` is the source notation; it does **not** by itself force your Lean theorem surface to be primitive `Float`. Preserve the task's numeric intent and every obligation when choosing a layer.
- For float-using tasks, keep `Float` for the executable implementation and ground unit tests. `native_decide` can check closed goals with an executable `Decidable` instance in `example` tests (never inside a theorem's proof, where it earns zero); `#eval` evaluates expressions. Passing ground tests does not prove a universally quantified property.
- Where the Python program's intent is mathematical rather than specifically about IEEE-754 behavior, state property, correctness and equivalence theorems over `Real` or `Rat` using Mathlib's proof libraries. Use `Int` / `Nat` for discrete tasks as appropriate. Define the corresponding mathematical implementation and prove its properties; changing a numeric type alone does not connect two implementations.
- You may organize numeric models under names such as `FloatLayer`, `RealLayer`, `RatLayer`, `FloatSpecLayer`, `FleanLayer` and `IntervalLayer`. `Real` and `Rat` support exact mathematical models; use a rational restriction only when it preserves the task's admissible domain. An IEEE-754 model must represent the required floating-point behavior. An interval model is suitable for a bounds-style obligation, but bounds cannot replace a required exact result. These names are modelling conventions: the current theorem-coverage evaluator has no accepted-layer list or automatic cross-layer credit. Naming a layer does not prove equivalence or guarantee coverage credit.
- FloatSpec, Flean and Interval are not preinstalled in this sandbox: it provides Lean 4.22.0 and Mathlib v4.22.0. To use an external layer, provide self-contained definitions that compile in the evaluation environment; naming a layer or importing an unavailable library does not suffice.
- Primitive `Float` has an opaque underlying numeric model and opaque arithmetic operations, so the kernel cannot reduce those operations to prove general arithmetic laws. Structural or reflexive claims involving `Float` can still be proved. A theorem establishes the proposition stated for its chosen numeric model. To claim a result about another model or the Python implementation, state and prove the required correspondence; changing a type alone is insufficient. Any theorem left `sorry` earns **zero** proof-completion credit for that theorem.
- Where NaN, infinities, signed zero, overflow, underflow or rounding are part of the specification, model the required behavior explicitly. A finiteness hypothesis is valid only when the task's admissible inputs already guarantee it, or when the excluded cases are covered separately. `Option` / `Except` results and error bounds must preserve the required behavior, not replace a stronger obligation with an easier one.
- Changing the layer changes the numeric model under the declared intent, not the obligation: do not drop, weaken or narrow an obligation about the Python program in order to make a proof go through. Keep the required input domain and exceptional cases; do not strengthen preconditions merely to make the proof easier.

## Proof Policy (scored -- read carefully)

- **Prove every theorem you state, and attempt every proof.** A theorem counts as proven only if the Lean kernel checks it using no axioms beyond `propext`, `Classical.choice` and `Quot.sound`. A proof that uses `sorry`, `admit`, `native_decide` (it trusts compiled code instead of the kernel) or a new `axiom`, or that relies on a lemma or definition proved that way, earns zero. Use `native_decide` only in `example` tests, never inside a theorem's proof.
- If, after a genuine attempt, you cannot close a proof, you MAY leave `:= sorry` so the file still compiles -- but that theorem earns **zero** proof-completion credit.
- Do not game the score: stating fewer, weaker, or trivial theorems to raise your proven fraction loses you credit elsewhere -- your theorem *statements* are separately judged for semantic fidelity to the Python program against a hidden human reference.
- Do not introduce `axiom` declarations or other escape hatches; they violate the task policy.

## Available Tools

- **Lean 4** (v4.22.0) is installed
- **Mathlib** is available (`import Mathlib`)
- Compile your file: `cd /home/user/lean_project && lake env lean Veribench/{lean_stem}.lean`
- The Lean project is at `/home/user/lean_project/`

## Success Criteria (in priority order)

1. **Hard gate -- it must compile:** `lake env lean` must exit 0 with no errors. A non-compiling file scores 0 overall.
2. **Proof completion:** maximize the fraction of your stated theorems proven under the Proof Policy (no `sorry`, `admit`, `native_decide` or new axiom, directly or through a helper); this fraction is a multiplicative factor of your score, and all-`sorry` gives 0.
3. **Statement fidelity:** your theorem statements should capture the true semantics of the Python program (properties, pre/post-conditions, functional-imperative equivalence).

A file that merely compiles with every proof left as `sorry` satisfies (1) but scores zero on (2) -- that is a failing result, not a success.
"""
    return _completion.add_completion_reminder(
        instruction, [f"/home/user/lean_project/Veribench/{lean_stem}.lean"])


def generate_test_sh(lean_stem: str, canary: str) -> str:
    """Generate test.sh by substituting placeholders in the template."""
    template = (TEMPLATE_DIR / "test.sh").read_text()
    solution_file = f"/home/user/lean_project/Veribench/{lean_stem}.lean"
    lean_rel_path = f"Veribench/{lean_stem}.lean"
    return (
        template
        .replace("__SOLUTION_FILE__", solution_file)
        .replace("__LEAN_REL_PATH__", lean_rel_path)
        .replace("__CANARY__", canary)
    )


def generate_solve_sh(lean_stem: str) -> str:
    """Generate solve.sh (oracle) that copies gold ref to expected output."""
    return (
        "#!/bin/bash\n"
        "# Oracle solution: copy known-good Lean file to the expected output path\n"
        f"cp /solution/gold.lean /home/user/lean_project/Veribench/{lean_stem}.lean\n"
    )


def parse_args():
    """CLI args. Defaults reproduce the historical behaviour exactly (regenerate ../tasks)."""
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", type=Path, default=OUTPUT_DIR,
                    help=f"Task-pack output directory (default: {OUTPUT_DIR})")
    ap.add_argument("--only-splits", nargs="*", default=None,
                    help="Restrict generation to these top-level splits (default: all)")
    return ap.parse_args()


def main():
    args = parse_args()
    out_dir = args.output
    only_splits = set(args.only_splits) if args.only_splits else None

    # Clean and recreate output dir
    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True)

    # Read shared resources
    judge_prompt = JUDGE_PROMPT.read_text()
    dockerfile = (TEMPLATE_DIR / "Dockerfile").read_text()
    task_toml = (TEMPLATE_DIR / "task.toml").read_text()
    setup_script = SETUP_SCRIPT.read_text()

    py_files = find_py_files()
    print(f"Found {len(py_files)} Python files in {PY_SRC}")

    generated = 0
    skipped = []
    split_counts: dict[str, int] = {}

    for py_path in py_files:
        lean_path = py_to_lean_path(py_path)
        task_id = make_task_id(py_path)
        lean_stem = lean_path.stem
        split = extract_split(py_path)

        if only_splits is not None and split not in only_splits:
            continue

        if not lean_path.exists():
            rel = str(py_path.relative_to(PY_SRC))
            print(f"  WARNING: No gold Lean file for {rel} → skipping")
            skipped.append(rel)
            continue

        # Read sources
        py_content = py_path.read_text()
        gold_content = lean_path.read_text()
        canary = extract_canary(gold_content)

        # Create task directory layout
        task_dir = out_dir / task_id
        (task_dir / "environment").mkdir(parents=True)
        (task_dir / "tests").mkdir(parents=True)
        (task_dir / "solution").mkdir(parents=True)

        # Write all task files
        (task_dir / "instruction.md").write_text(generate_instruction(py_content, lean_stem))
        (task_dir / "task.toml").write_text(task_toml)
        (task_dir / "environment" / "Dockerfile").write_text(dockerfile)
        (task_dir / "environment" / "veribench_setup.sh").write_text(setup_script)
        (task_dir / "tests" / "test.sh").write_text(generate_test_sh(lean_stem, canary))
        (task_dir / "tests" / "gold.lean").write_text(gold_content)
        (task_dir / "tests" / "judge_prompt.txt").write_text(judge_prompt)
        (task_dir / "solution" / "solve.sh").write_text(generate_solve_sh(lean_stem))
        (task_dir / "solution" / "gold.lean").write_text(gold_content)

        # Make scripts executable
        os.chmod(task_dir / "tests" / "test.sh", 0o755)
        os.chmod(task_dir / "solution" / "solve.sh", 0o755)

        split_counts[split] = split_counts.get(split, 0) + 1
        generated += 1

    # Summary
    print(f"\n{'='*50}")
    print(f"Generated {generated} task directories in {out_dir}")
    print(f"\nPer-split breakdown:")
    for split in sorted(split_counts):
        print(f"  {split}: {split_counts[split]}")
    if skipped:
        print(f"\nSkipped {len(skipped)} files (no matching gold Lean):")
        for s in skipped:
            print(f"  - {s}")
    print(f"{'='*50}")


if __name__ == "__main__":
    main()
