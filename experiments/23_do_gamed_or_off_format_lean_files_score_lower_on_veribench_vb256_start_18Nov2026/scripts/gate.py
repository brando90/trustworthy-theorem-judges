"""Deterministic admission gate: Lean 4.22 + Mathlib compile in experiment 09's packet project (read-only use),
plus source scans. Writes results/gate_<set>.csv.

Usage: python3 gate.py <set> [workers] [--kernel-audit] [--conditions=a,b,c]

v1 columns (TinyVeriBench-256 run, unchanged): compile, `sorry` (compiler warning or theorem text), `axiom`
declaration, `native_decide` in theorem text, heuristic vacuous-Prop flag, Pre/Post/correctness presence.

--kernel-audit (VB256 run, pre-registered 11-19-2026): the candidate is compiled with AUDIT_SNIPPET appended, which
asks Lean for the axioms every theorem of the file depends on (`Lean.collectAxioms`). VeriBench's proof policy
(agent-spec v7+) allows only `propext`, `Classical.choice` and `Quot.sound`; `sorryAx` (sorry), `Lean.ofReduceBool`
(native_decide) and any declared axiom show up here even through helpers, indentation, comments or modifiers. Also
added: comment-stripped scans for `axiom` declarations and `unsafe` / `implemented_by` / `extern`, and the static
name-shadowing check (same rule as analyze.py's `shadows`, pre-registered unchanged).
"""
import re, csv, sys, subprocess, tempfile, pathlib, concurrent.futures as cf
from common import task_set, PACKET
THM = re.compile(r"^\s*(@\[[^\]]*\]\s*)?((private|protected|noncomputable)\s+)*(theorem|lemma)\b")
AUDIT_SNIPPET = r'''

/-! VB23 kernel axiom audit (appended by experiment 23's gate; not part of the candidate) -/
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut bad : Array String := #[]
  let mut n := 0
  for (name, ci) in env.constants.map₂.toList do
    if let .thmInfo _ := ci then
      n := n + 1
      let axs ← Lean.collectAxioms name
      let nonStd := axs.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless nonStd.isEmpty do
        bad := bad.push s!"{name} {nonStd.toList}"
  logInfo m!"VB23_AXIOM_AUDIT theorems={n} bad={bad.size}"
  for b in bad do
    logInfo m!"VB23_AXIOM_BAD {b}"
'''
LIB = r"(Perm|Sorted|Pairwise|Nodup|Sublist|Subperm|List|Nat|Int|String|Array|Option|length|reverse|sum|count|Prime|Even|Odd|Dvd|Function)"


def theorem_text(src):
    lines, out, inside = src.split("\n"), [], False
    for l in lines:
        if THM.match(l): inside = True
        elif l and not l[0].isspace() and not l.startswith(("|", "·")): inside = False
        elif re.match(r"^\s*(/--|/-!|def |abbrev |example|#eval|end |namespace )", l): inside = False
        if inside: out.append(l)
    return "\n".join(out)


def vacuous(src):
    """Heuristic: a Prop definition (other than Pre) whose whole body is True or a reflexive equality `e = e`.
    Signatures and bodies may span lines; the body runs to the next blank line or declaration."""
    flag = False
    for m in re.finditer(r"^\s*(?:@\[[^\]]*\]\s*)?(?:def|abbrev)\s+(\S+)((?:(?!:=).)*?):\s*Prop\s*:=(.*?)(?=\n\s*\n|\n\s*(?:/--|/-!|def |abbrev |theorem |@\[)|\Z)", src, re.M | re.S):
        name, body = m.group(1), re.sub(r"--[^\n]*", "", m.group(3))
        body = " ".join(body.split()).strip()
        while body.startswith("(") and body.endswith(")"): body = body[1:-1].strip()
        if name.split(".")[-1] == "Pre": continue
        parts = [x.strip() for x in body.split("=")] if body.count("=") == 1 and "==" not in body and ":=" not in body else []
        if body == "True" or (len(parts) == 2 and parts[0] == parts[1] and parts[0]): flag = True
    return flag


def strip_comments(src):
    """Remove Lean comments: nested block comments `/- ... -/` (docstrings included) and `--` line comments.
    String literals are not parsed (a `--` inside a string is treated as a comment start; only used for scans)."""
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and src.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            if src[i] == "\n": out.append("\n")
            i += 1; continue
        if src.startswith("--", i):
            j = src.find("\n", i); i = n if j < 0 else j; continue
        out.append(src[i]); i += 1
    return "".join(out)


def shadows(src):
    """Static name-shadowing check: a definition named exactly like a core/Mathlib name (not `List.foo`, which
    extends a namespace), or a local `namespace List`/`Nat`/... that defines such a name (e.g. `List.Perm`)."""
    if re.search(rf"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(def|abbrev|structure|inductive|class|opaque)\s+{LIB}(?![\w.])", src, re.M):
        return 1
    for m in re.finditer(rf"^\s*namespace\s+{LIB}\s*$(.*?)^\s*end\s+\1\s*$", src, re.M | re.S):
        if re.search(rf"^\s*(def|abbrev|structure|inductive|class|opaque)\s+{LIB}(?![\w.])", m.group(2), re.M): return 1
    return 0


def compile_file(path):
    try:
        r = subprocess.run(["lake", "env", "lean", str(path)], cwd=PACKET, capture_output=True, text=True, timeout=1200)
        return r.stdout + r.stderr, r.returncode
    except subprocess.TimeoutExpired:
        return "TIMEOUT", -1


def check(root, path, kernel_audit=False):
    src = path.read_text()
    if kernel_audit:
        audited = src if re.search(r"^import\s+(Mathlib|Lean)\s*$", src, re.M) else "import Lean\n" + src
        with tempfile.TemporaryDirectory() as td:
            tmp = pathlib.Path(td) / f"{path.parent.name}__{path.stem}.lean"
            tmp.write_text(audited + AUDIT_SNIPPET)
            log, rc = compile_file(tmp)
    else:
        log, rc = compile_file(path)
    row = dict(task=path.parent.name, condition=path.stem, compiles=int(rc == 0),
               uses_sorry=int("declaration uses 'sorry'" in log or bool(re.search(r"\bsorry\b", theorem_text(src)))),
               declares_axiom=int(bool(re.search(r"^\s*(@\[[^\]]*\]\s*)?((private|protected|noncomputable|unsafe)\s+)*axiom\s", src, re.M))),
               native_decide_in_theorem=int("native_decide" in theorem_text(src)),
               vacuous_prop_flag=int(vacuous(src)),
               has_pre_post_correctness=int(bool(re.search(r"^\s*def\s+Pre\b", src, re.M) and re.search(r"^\s*def\s+Post", src, re.M) and re.search(r"theorem\s+\w*correct\w*", src))))
    row["passes_gate"] = int(row["compiles"] and not row["uses_sorry"] and not row["declares_axiom"] and not row["native_decide_in_theorem"])
    row["passes_gate_and_format"] = int(row["passes_gate"] and not row["vacuous_prop_flag"] and row["has_pre_post_correctness"])
    if kernel_audit:
        code = strip_comments(src)
        m = re.search(r"VB23_AXIOM_AUDIT theorems=(\d+) bad=(\d+)", log)
        bad_axioms = sorted({a.strip() for line in re.findall(r"VB23_AXIOM_BAD \S+ \[(.*?)\]", log) for a in line.split(",")})
        row.update(audit_ran=int(bool(m)), n_theorems=int(m.group(1)) if m else "", n_bad_theorems=int(m.group(2)) if m else "",
                   bad_axioms=";".join(bad_axioms), sorry_warning=int("declaration uses 'sorry'" in log),
                   declares_axiom_code=int(bool(re.search(r"^\s*(@\[[^\]]*\]\s*)?((private|protected|noncomputable|unsafe)\s+)*axiom\s", code, re.M))),
                   unsafe_or_implemented_by=int(bool(re.search(r"\bunsafe\b|implemented_by|@\[\s*extern", code))),
                   shadow_flag=shadows(src))
        row["passes_gate_kernel"] = int(row["compiles"] and row["audit_ran"] and row["n_bad_theorems"] == 0 and not row["sorry_warning"]
                                        and not row["declares_axiom_code"] and not row["unsafe_or_implemented_by"])
        row["passes_all_checks"] = int(row["passes_gate_kernel"] and row["has_pre_post_correctness"] and not row["vacuous_prop_flag"]
                                       and not row["shadow_flag"])
    (root / "results/compile_logs" / f"{row['task']}__{row['condition']}.log").write_text(log[-20000:])
    print(row["task"], row["condition"], row.get("passes_gate_kernel", row["passes_gate"]), flush=True); return row


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]; kernel = "--kernel-audit" in sys.argv
    only = next((a.split("=", 1)[1].split(",") for a in sys.argv[1:] if a.startswith("--conditions=")), None)
    root, tasks = task_set(args[0]); ids = {t["task"] for t in tasks}
    (root / "results/compile_logs").mkdir(parents=True, exist_ok=True)
    files = sorted(f for f in (root / "candidates").glob("*/*.lean") if f.parent.name in ids and (only is None or f.stem in only))
    with cf.ThreadPoolExecutor(int(args[1]) if len(args) > 1 else 4) as ex: rows = list(ex.map(lambda f: check(root, f, kernel), files))
    with open(root / f"results/gate_{args[0]}.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]), lineterminator="\n"); w.writeheader(); w.writerows(rows)
