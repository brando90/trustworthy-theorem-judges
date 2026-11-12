# TLDR: Deterministic, stdlib-only extractor of the pre-registered file-side criteria C1-C13 (CRITERIA.md section 2-3) for one Lean candidate file, its reference Lean file and its task's Python source.
"""Experiment 110 criterion extractor (stdlib only; run with python3 -I).

Usage as a module: features(candidate_text, reference_text, python_text) -> dict.
Usage as a script: python3 -I extract_criteria.py CAND.lean REF.lean TASK.py  (prints JSON).

Interpretation choices where CRITERIA.md is silent are fixed here and listed in INTERPRETATION below.
"""
import json
import math
import re
import statistics
import sys

INTERPRETATION = [
    "Declaration starts may be indented (line beginning after optional whitespace); the terminators namespace/section/end/#eval/#guard/open must be at column 0, as written in CRITERIA.md step 2.",
    "String literals are skipped when stripping comments, so '--' inside a string is not a comment.",
    "Statement text includes the theorem keyword and the declared name (literal reading of step 3); C4 token counts and identifier sets therefore include the name.",
    "Numeric literals match neither token alternative of the step-4 regex and are dropped, as the regex implies.",
    "C5 binder groups: ( or { followed by one or more names and ':' before the top-level ':' of the statement.",
    "C6 arrows are searched only after the top-level ':' (the pre-colon region holds the binder types); if there is no top-level ':' the whole statement text is searched.",
    "C7 'binder' = any pre-colon bracketed binder group ((, {, [, or ⦃), or fun/λ anywhere; 'quantifier' = ∀, ∃, forall, exists.",
    "C8 names: last dotted component of a def/abbrev, lowercased, ends with 'pre' or 'precondition' (resp. 'post' or 'postcondition'); the third point needs one statement whose identifiers contain a pre name and a post name and that contains → or ->.",
    "C9 counts 'example' declarations plus lines starting (after whitespace) with '#eval' or '#guard' followed by whitespace (#guard_msgs is a different command and is not counted).",
    "Main function: Python top-level 'def name' at column 0 (also 'async def'), name not starting with '_', not 'main', not 'test_*'. Lean matches are def/abbrev names whose normalized form (lowercase, '_' removed, last dotted component) equals or contains the normalized Python name.",
    "C11/C12 'mentions main': an identifier token whose '_'-removed form equals a matched Lean main name's normalized form. In C12 such tokens become MAIN on both sides.",
    "Step-6 parser fix (before freezing): a ':=' that closes a depth-0 'let'/'have' inside a statement does not end the statement (the 1_bisect_left__agent2 check truncated two statements at 'let i').",
    "Amendment A1 (10-09-2026, step-6 check on my_add.lean, before any pool/FM run): the literal step-5 rule picks the harness helper 'pre'/'pre_condition' as the main function in about a third of VBV1 Python sources, so C11/C12 are also computed with those helpers (and pre_*/post_* names) skipped (C11_A1, C12_A1); both are reported, the pre-registered one is primary.",
    "C12: Jaccard of two empty sets is 0; candidate with no statements gives 0; reference with no statements gives None (unavailable for that file).",
]

DECL_KW = ("def", "abbrev", "instance", "structure", "inductive", "class", "theorem", "lemma", "example")
DEF_KW = ("def", "abbrev", "instance", "structure", "inductive", "class")
MODIFIERS = ("private", "protected", "noncomputable", "partial", "unsafe")
TERMINATORS = ("namespace", "section", "end", "#eval", "#guard", "open")
STOP = {"Nat", "Int", "List", "Bool", "Prop", "Type", "True", "False", "fun", "Option", "some", "none",
        "Array", "String", "Char", "Float", "theorem", "lemma", "def", "by"}
LEAN_KW = {"theorem", "lemma", "def", "by", "fun", "have", "show", "let", "in", "if", "then", "else", "match",
           "with", "do", "return", "where", "at", "from", "forall", "exists", "calc", "private", "protected",
           "noncomputable", "partial", "unsafe", "instance", "structure", "inductive", "class", "abbrev",
           "example", "Sort", "Type", "Prop", "mut", "for", "unless", "deriving", "extends", "open", "namespace",
           "section", "end", "variable", "universe", "import", "λ"}
TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.!?]*|[^\sA-Za-z0-9_]")
IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.!?]*$")
OPEN = "([{⟨⦃"
CLOSE = ")]}⟩⦄"


def strip_comments(text):
    """Return (stripped_text, n_comment_chars). Handles nested /- -/ and -- line comments; skips string literals."""
    out = []
    i, n, depth, ccount = 0, len(text), 0, 0
    while i < n:
        if depth > 0:
            if text.startswith("/-", i):
                depth += 1; i += 2; ccount += 2; continue
            if text.startswith("-/", i):
                depth -= 1; i += 2; ccount += 2; continue
            if text[i] == "\n":
                out.append("\n")
            ccount += 1; i += 1; continue
        c = text[i]
        if c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i:j + 1]); i = j + 1; continue
        if text.startswith("/-", i):
            depth = 1; i += 2; ccount += 2; continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            ccount += j - i; i = j; continue
        out.append(c); i += 1
    return "".join(out), ccount


_DECL_START = re.compile(r"^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:(?:%s)[ \t]+)*(%s)\b" % ("|".join(MODIFIERS), "|".join(DECL_KW)))
_TERM_START = re.compile(r"^(?:namespace|section|end|open)\b|^#(?:eval|guard)\b")


def declarations(stripped):
    """List of (kind, text) declarations per CRITERIA.md step 2."""
    decls, cur_kind, cur = [], None, []
    for line in stripped.split("\n"):
        m = _DECL_START.match(line)
        if m:
            if cur_kind:
                decls.append((cur_kind, "\n".join(cur)))
            cur_kind, cur = m.group(1), [line[m.start(1):]]
            continue
        if _TERM_START.match(line):
            if cur_kind:
                decls.append((cur_kind, "\n".join(cur)))
            cur_kind, cur = None, []
            continue
        if cur_kind:
            cur.append(line)
    if cur_kind:
        decls.append((cur_kind, "\n".join(cur)))
    return decls


def decl_name(text):
    m = re.match(r"\s*\w+\s+([^\s(\[{:⦃⟨]+)", text)
    return m.group(1) if m else ""


def split_statement(text):
    """Return (statement_text, proof_text): up to first depth-0 ':='; else to 'where' or a leading '|'."""
    depth, pending = 0, 0
    for i, c in enumerate(text):
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0 and (text.startswith("let", i) or text.startswith("have", i)) \
                and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_.'")) \
                and re.match(r"(?:let|have)\s", text[i:]):
            pending += 1
        elif depth == 0 and text.startswith(":=", i):
            if pending:
                pending -= 1
                continue
            return text[:i], text[i + 2:]
    m = re.search(r"\bwhere\b|\n[ \t]*\|", text)
    if m:
        return text[:m.start()], text[m.start():]
    return text, ""


def top_colon(stmt):
    """Index of the first ':' at bracket depth 0 that is not part of ':='; -1 if none."""
    depth = 0
    for i, c in enumerate(stmt):
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth = max(0, depth - 1)
        elif c == ":" and depth == 0 and not stmt.startswith(":=", i):
            return i
    return -1


def tokens(stmt):
    return TOKEN_RE.findall(stmt)


def norm_ident(tok):
    return tok.split(".")[-1].lower() if "." in tok.strip(".") else tok.lower()


def identifiers(stmt):
    out = set()
    for t in tokens(stmt):
        if IDENT_RE.match(t) and t not in STOP and t not in LEAN_KW:
            last = [p for p in t.split(".") if p]
            if not last:
                continue
            nt = last[-1].lower()
            if nt in {w.lower() for w in STOP} or nt in LEAN_KW:
                continue
            out.add(nt)
    return out


_BINDER_GROUP = re.compile(r"[({]\s*[^\s:(){}\[\]]+(?:\s+[^\s:(){}\[\]]+)*\s*:(?!=)")
_ANY_BINDER = re.compile(r"[({\[⦃]\s*[^\s:(){}\[\]]+(?:\s+[^\s:(){}\[\]]+)*\s*:(?!=)")
_ARROW = re.compile(r"→|->|↔|<->")
_IMPL = re.compile(r"→|->")
_QUANT = re.compile(r"∀|∃|\bforall\b|\bexists\b")
_FUN = re.compile(r"\bfun\b|λ")


A1_SKIP = {"pre", "post", "check", "precondition", "postcondition"}


def python_main(py_text, rule="prereg"):
    """rule='prereg': CRITERIA.md step 5 literally. rule='A1': amendment A1 (10-09-2026, found in the step-6
    extractor check before any pool/FM criterion value was computed) also skips VeriBench harness helpers whose
    '_'-removed lowercase name is pre, post, check, precondition or postcondition, or that start with pre_/post_."""
    for line in py_text.split("\n"):
        m = re.match(r"(?:async\s+)?def\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(", line)
        if m:
            name = m.group(1)
            if name.startswith("_") or name == "main" or name.startswith("test_"):
                continue
            if rule == "A1" and (name.lower().replace("_", "") in A1_SKIP or name.lower().startswith(("pre_", "post_"))):
                continue
            return name
    return None


def lean_main_names(def_names, py_name):
    if not py_name:
        return set()
    pn = py_name.lower().replace("_", "")
    out = set()
    for d in def_names:
        dn = d.split(".")[-1].lower().replace("_", "")
        if dn and (dn == pn or pn in dn):
            out.add(dn)
    return out


def parse(text, py_name):
    stripped, ccount = strip_comments(text)
    decls = declarations(stripped)
    def_names = [decl_name(t) for k, t in decls if k in ("def", "abbrev")]
    mains = lean_main_names(def_names, py_name)
    stmts = []
    for k, t in decls:
        if k in ("theorem", "lemma"):
            s, p = split_statement(t)
            stmts.append({"stmt": s, "proof": p, "idents": identifiers(s), "ntok": len(tokens(s))})
    return {"stripped": stripped, "ccount": ccount, "decls": decls, "def_names": def_names, "mains": mains, "stmts": stmts}


def mentions_main(idents, mains):
    return any(i.replace("_", "") in mains for i in idents)


def main_norm_set(idents, mains):
    return {("MAIN" if i.replace("_", "") in mains else i) for i in idents}


def jaccard(a, b):
    u = a | b
    return len(a & b) / len(u) if u else 0.0


def features(cand_text, ref_text, py_text):
    f = _features(cand_text, ref_text, py_text, "prereg")
    a1 = _features(cand_text, ref_text, py_text, "A1")
    f["C11_A1"], f["C12_A1"] = a1["C11"], a1["C12"]
    f["diag"]["py_main_A1"] = a1["diag"]["py_main"]
    f["diag"]["lean_main_matched_A1"] = a1["diag"]["lean_main_matched"]
    f["diag"]["ref_main_matched_A1"] = a1["diag"]["ref_main_matched"]
    return f


def _features(cand_text, ref_text, py_text, rule):
    py_name = python_main(py_text, rule) if py_text is not None else None
    c = parse(cand_text, py_name)
    stmts = c["stmts"]
    n = len(stmts)
    lines = [l for l in c["stripped"].split("\n") if l.strip()]
    pre_names = {d.split(".")[-1].lower() for d in c["def_names"] if d.split(".")[-1].lower().endswith(("pre", "precondition"))}
    post_names = {d.split(".")[-1].lower() for d in c["def_names"] if d.split(".")[-1].lower().endswith(("post", "postcondition"))}
    f = {}
    f["C1"] = len(lines)
    f["C2"] = sum(1 for k, _ in c["decls"] if k in DEF_KW)
    f["C3"] = n
    f["C4"] = float(statistics.median([s["ntok"] for s in stmts])) if n else 0.0
    q = cond = ground = 0
    for s in stmts:
        st = s["stmt"]
        tc = top_colon(st)
        pre_region = st[:tc] if tc >= 0 else ""
        post_region = st[tc + 1:] if tc >= 0 else st
        has_q = bool(re.search(r"∀|\bforall\b", st)) or bool(_BINDER_GROUP.search(pre_region))
        q += has_q
        cond += bool(_ARROW.search(post_region))
        any_binder = bool(_ANY_BINDER.search(pre_region)) or bool(_FUN.search(st))
        ground += (not any_binder) and (not _QUANT.search(st)) and (not _ARROW.search(st))
    f["C5"] = q / n if n else 0.0
    f["C6"] = cond / n if n else 0.0
    f["C7"] = ground / n if n else 0.0
    scaffold = int(bool(pre_names)) + int(bool(post_names))
    if pre_names and post_names and any((s["idents"] & pre_names) and (s["idents"] & post_names) and _IMPL.search(s["stmt"]) for s in stmts):
        scaffold += 1
    f["C8"] = scaffold
    n_example = sum(1 for k, _ in c["decls"] if k == "example")
    n_cmd = len(re.findall(r"(?m)^[ \t]*#(?:eval|guard)(?=\s)", c["stripped"]))
    f["C9"] = n_example + n_cmd
    f["C10"] = (sum(1 for s in stmts if re.search(r"\b(?:sorry|admit)\b", s["proof"])) / n) if n else 0.0
    f["C11"] = (sum(1 for s in stmts if mentions_main(s["idents"], c["mains"])) / n) if n else 0.0
    r = parse(ref_text, py_name) if ref_text is not None else None
    if r is None or not r["stmts"]:
        f["C12"] = None
    else:
        cs = [main_norm_set(s["idents"], c["mains"]) for s in stmts]
        vals = []
        for rs in r["stmts"]:
            rset = main_norm_set(rs["idents"], r["mains"])
            vals.append(max((jaccard(rset, x) for x in cs), default=0.0))
        f["C12"] = sum(vals) / len(vals)
    f["C13"] = math.log2((n + 1) / (len(r["stmts"]) + 1)) if r is not None else None
    # diagnostics (not counted)
    defs = [d.split(".")[-1] for d in c["def_names"] if d]
    f["diag"] = {
        "comment_density": c["ccount"] / len(cand_text) if cand_text else 0.0,
        "snake_case_def_frac": (sum(1 for d in defs if re.fullmatch(r"[a-z0-9_']+", d)) / len(defs)) if defs else None,
        "decidable_typeclass_structure": len(re.findall(r"\bDecidable\b|\binstance\b|\bclass\b|\bstructure\b", c["stripped"])),
        "native_decide": len(re.findall(r"\bnative_decide\b", c["stripped"])),
        "mathlib_import": bool(re.search(r"(?m)^import\s+Mathlib", cand_text)),
        "py_main": py_name,
        "lean_main_matched": bool(c["mains"]),
        "ref_main_matched": bool(r["mains"]) if r is not None else None,
        "n_ref_statements": len(r["stmts"]) if r is not None else None,
    }
    return f


if __name__ == "__main__":
    def rd(p):
        with open(p, encoding="utf-8", errors="replace") as fh:
            return fh.read()
    cand, ref, py = sys.argv[1], sys.argv[2], sys.argv[3]
    out = features(rd(cand), rd(ref), rd(py))
    p = parse(rd(cand), python_main(rd(py), "A1"))
    out["_debug"] = {"decls": [(k, decl_name(t)) for k, t in p["decls"]], "mains": sorted(p["mains"]),
                     "statements": [s["stmt"].strip()[:160] for s in p["stmts"]]}
    print(json.dumps(out, indent=1, ensure_ascii=False))
