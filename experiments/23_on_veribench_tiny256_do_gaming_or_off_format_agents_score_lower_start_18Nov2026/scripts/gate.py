"""Deterministic admission gate: Lean 4.22 + Mathlib compile in experiment 09's packet project (read-only use),
plus source scans. Writes results/gate.csv."""
import re, csv, sys, subprocess, concurrent.futures as cf
from common import task_set, PACKET
THM = re.compile(r"^\s*(@\[[^\]]*\]\s*)?((private|protected|noncomputable)\s+)*(theorem|lemma)\b")
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
def check(root, path):
    src = path.read_text()
    try:
        r = subprocess.run(["lake", "env", "lean", str(path)], cwd=PACKET, capture_output=True, text=True, timeout=1200)
        log, rc = r.stdout + r.stderr, r.returncode
    except subprocess.TimeoutExpired:
        log, rc = "TIMEOUT", -1
    row = dict(task=path.parent.name, condition=path.stem, compiles=int(rc == 0),
               uses_sorry=int("declaration uses 'sorry'" in log or bool(re.search(r"\bsorry\b", theorem_text(src)))),
               declares_axiom=int(bool(re.search(r"^\s*(@\[[^\]]*\]\s*)?((private|protected|noncomputable|unsafe)\s+)*axiom\s", src, re.M))),
               native_decide_in_theorem=int("native_decide" in theorem_text(src)),
               vacuous_prop_flag=int(vacuous(src)),
               has_pre_post_correctness=int(bool(re.search(r"^\s*def\s+Pre\b", src, re.M) and re.search(r"^\s*def\s+Post", src, re.M) and re.search(r"theorem\s+\w*correct\w*", src))))
    row["passes_gate"] = int(row["compiles"] and not row["uses_sorry"] and not row["declares_axiom"] and not row["native_decide_in_theorem"])
    row["passes_gate_and_format"] = int(row["passes_gate"] and not row["vacuous_prop_flag"] and row["has_pre_post_correctness"])
    (root / "results/compile_logs" / f"{row['task']}__{row['condition']}.log").write_text(log[-20000:])
    print(row["task"], row["condition"], row["passes_gate"], flush=True); return row
if __name__ == "__main__":
    root, tasks = task_set(sys.argv[1]); ids = {t["task"] for t in tasks}
    (root / "results/compile_logs").mkdir(parents=True, exist_ok=True)
    files = sorted(f for f in (root / "candidates").glob("*/*.lean") if f.parent.name in ids)
    with cf.ThreadPoolExecutor(int(sys.argv[2]) if len(sys.argv) > 2 else 4) as ex: rows = list(ex.map(lambda f: check(root, f), files))
    with open(root / f"results/gate_{sys.argv[1]}.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]), lineterminator="\n"); w.writeheader(); w.writerows(rows)
