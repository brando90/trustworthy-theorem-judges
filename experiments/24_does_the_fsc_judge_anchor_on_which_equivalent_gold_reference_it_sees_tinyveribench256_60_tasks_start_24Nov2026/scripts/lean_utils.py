"""Lean text helpers of experiment 24: proof stripping, statement extraction and statement similarity.

Use: imported by build_refs.py, gen_alt.py and analyze.py. Needs only python3. `replace_proofs` is experiment 23's build_variants.replace_proofs.
"""
import re, difflib
THM = re.compile(r"^(@\[[^\]]*\]\s*)?((private|protected|noncomputable)\s+)*(theorem|lemma)\s+(\S+)")


def proof_blocks(lines):
    i = 0
    while i < len(lines):
        if THM.match(lines[i]):
            j = i + 1
            while j < len(lines) and (lines[j].startswith((" ", "\t")) or lines[j].strip() == "" and j + 1 < len(lines) and lines[j + 1].startswith((" ", "\t"))):
                j += 1
            yield i, j
            i = j
        else:
            i += 1


def top_level_assign(decl):
    depth = 0
    for i, ch in enumerate(decl):
        if ch in "([{": depth += 1
        elif ch in ")]}": depth -= 1
        elif depth == 0 and decl.startswith(":=", i): return i
    return -1


def replace_proofs(text, proof="by sorry"):
    lines = text.split("\n"); out = []; last = 0
    for s, e in proof_blocks(lines):
        out += lines[last:s]
        decl = "\n".join(lines[s:e])
        k = top_level_assign(decl)
        head = decl[:k].rstrip() if k >= 0 else decl.rstrip()
        out.append(f"{head} := {proof}"); last = e
    out += lines[last:]
    return "\n".join(out)


def strip_comments(src):
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i): depth += 1; i += 2
        elif depth and src.startswith("-/", i): depth -= 1; i += 2
        elif depth: i += 1
        elif src.startswith("--", i):
            while i < n and src[i] != "\n": i += 1
        else: out.append(src[i]); i += 1
    return "".join(out)


DEF_PROP = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:def|abbrev)\s+(\S+)(?:(?!:=).)*?:\s*Prop\b", re.S | re.M)


def statements(src):
    """Normalized statement text: every theorem/lemma head (up to its top-level `:=`) and every `def ... : Prop` (head and body), comments removed, whitespace collapsed. Returned as a list in file order."""
    t = strip_comments(src)
    lines = t.split("\n")
    items = []
    blocks = list(proof_blocks(lines))
    for s, e in blocks:
        decl = "\n".join(lines[s:e]); k = top_level_assign(decl)
        items.append(" ".join((decl[:k] if k >= 0 else decl).split()))
    # Prop definitions: from a `def ... : Prop` line to the next blank line
    for m in re.finditer(r"^(?:@\[[^\]]*\]\s*)?(?:def|abbrev)\s+\S+[^\n]*?(?:\n(?![ \t]*\n)[^\n]*?)*?:\s*Prop\b.*?(?=\n\s*\n|\Z)", t, re.M | re.S):
        items.append(" ".join(m.group(0).split()))
    return items


def theorem_names(src):
    return [THM.match(l).group(5) for l in strip_comments(src).split("\n") if THM.match(l)]


def similarity(a_src, b_src):
    """difflib ratio between the normalized statement texts of two Lean files (identifiers kept, no renaming)."""
    a = "\n".join(statements(a_src)); b = "\n".join(statements(b_src))
    return difflib.SequenceMatcher(None, a, b, autojunk=False).ratio()
