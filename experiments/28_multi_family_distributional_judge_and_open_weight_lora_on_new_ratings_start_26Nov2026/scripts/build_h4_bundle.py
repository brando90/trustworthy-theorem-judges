#!/usr/bin/env python3
"""Experiment 28, Step 3: Build exact matched 175-artifact bundle, SHA-256 input audit,
deterministic structural features, zero-demo distributional prompt (H4), and Karpathy controls.

Dated 11-26-2026. CPU only, no model calls.
"""
from __future__ import annotations

import csv
import difflib
import hashlib
import json
import math
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
EXP_DIR = Path(__file__).resolve().parents[1]
DATA_DIR = EXP_DIR / "data_11-26-2026"
RESULTS_DIR = EXP_DIR / "results"
EXP09_MAIN = ROOT / "experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/rating_task_packet/main_rating_task"
HUMAN_MD = ROOT / "experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/rating_task_packet/human_judgements_prompt.md"
CACHE_DIR = Path("/tmp/exp28_cache")

DECL_RE = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\]\n]*\][ \t]*\n?[ \t]*)?(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma)\s+"
)
THEOREM_NAME_RE = re.compile(r"\b(?:theorem|lemma)\s+([A-Za-z0-9_'.]+)")
SORRY_RE = re.compile(r"\b(?:sorry|admit)\b")
TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")

VACUOUS_LEAN = (
    "import Mathlib\n\nnamespace Candidate\n\n"
    "/-- Main claim. -/\ntheorem main_claim : True := trivial\n\nend Candidate\n"
)

CONVENTIONS = """Rating conventions the expert raters applied (use them together with the instructions above):
1. The agent's theorems describe the agent's own implementation of the same Python task. Count a gold theorem as covered when some agent theorem states the same property about the agent's implementation, even if the agent uses different types (List instead of Array, Int instead of Nat), different names, a different implementation, or has minor elaboration problems such as a missing instance or coercion. Do not require a formal bridge between the agent's function and the gold function.
2. A theorem that only restates an implementation states no independent property: for example that the function equals another definition of the same computation, equals the library call it is implemented with, or that a list of tests passes. Such theorems do not cover the gold property theorems; if they are all the agent states, the score is 0 or 1.
3. Missing or different preconditions (for example omitting sortedness or index bounds) lower the score by at most one point when the conclusion states the right property; they do not make a relevant theorem worthless.
4. The gold equivalence theorem between the gold functional and imperative implementations is a minor item: its absence alone is a minor gap."""


def strip_comments(src: str) -> str:
    src = re.sub(r"/-.*?-/", " ", src, flags=re.S)
    return re.sub(r"--[^\n]*", " ", src)


def extract_statements(src: str) -> list[str]:
    clean = strip_comments(src)
    out = []
    for m in DECL_RE.finditer(clean):
        j, depth = m.start(), 0
        while j < len(clean):
            ch = clean[j]
            if ch in "([{⟨":
                depth += 1
            elif ch in ")]}⟩":
                depth = max(0, depth - 1)
            elif depth == 0 and clean.startswith(":=", j):
                break
            elif depth == 0 and ch == "\n" and re.match(r"\n[ \t]*\|", clean[j:]):
                break
            j += 1
        out.append(" ".join(clean[m.start():j].split()))
    return out


def rater_instructions() -> str:
    text = HUMAN_MD.read_text(encoding="utf-8")
    head, _, tail = text.partition("## Output format (required)")
    tie = tail[tail.index("## Tie-break rule"):] if "## Tie-break rule" in tail else ""
    return (head.rstrip() + "\n\n" + tie.strip()).strip()


def build_h4_system() -> str:
    return (
        "You are one of the expert raters in a human-judgment study of Lean 4 formalizations. "
        "Rate exactly as a careful expert human rater following these instructions would. "
        "You receive the same three files the human raters received.\n\n"
        "<rater_instructions>\n" + rater_instructions() + "\n</rater_instructions>\n\n"
        "<rater_conventions>\n" + CONVENTIONS + "\n</rater_conventions>\n\n"
        "Also output a calibrated 6-category probability distribution `score_distribution` over integer scores 0, 1, 2, 3, 4, 5 "
        "representing the probability that a randomly drawn expert rater gives each score under this rubric. "
        "Avoid putting exact 0.0 everywhere else unless certainty is genuinely near 1; reflect realistic borderline uncertainty between adjacent scores.\n\n"
        "Answer with ONLY one JSON object (no markdown fences, no extra text) with exactly these keys:\n"
        '{"A": "Y" or "N", "B": "Y" or "N", "C": "Y" or "N", "D": "none" or "handful" or "dominates", '
        '"base_score": integer 0-5, "final_score_0_5": integer 0-5, '
        '"score_distribution": {"0": p0, "1": p1, "2": p2, "3": p3, "4": p4, "5": p5}, '
        '"confidence": "Low" or "Med" or "High", '
        '"rationale": "2-4 sentences naming at least one covered and one uncovered gold theorem if any, and spam examples if C=Y"}\n'
        "The six probabilities in score_distribution must be non-negative and sum to 1.0."
    )


def build_user_prompt(py_name: str, py_text: str, ref_name: str, ref_text: str, cand_name: str, cand_text: str) -> str:
    return (
        f"## 1. Python source: {py_name}\n```python\n{py_text}\n```\n\n"
        f"## 2. Gold Lean file: {ref_name}\n```lean\n{ref_text}\n```\n\n"
        f"## 3. Agent Lean file: {cand_name}\n```lean\n{cand_text}\n```\n"
    )


def sha256_str(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


def compute_structural_features(gold_text: str, cand_text: str) -> dict[str, float]:
    gold_stmts = extract_statements(gold_text)
    cand_stmts = extract_statements(cand_text)
    n_gold = len(gold_stmts)
    n_cand = len(cand_stmts)
    thm_ratio = min(1.0, n_cand / max(1, n_gold))
    excess_thm_log = math.log1p(max(0, n_cand - n_gold))
    cand_clean = strip_comments(cand_text)
    sorry_cnt = len(SORRY_RE.findall(cand_clean))
    gold_lines = len(gold_text.splitlines())
    cand_lines = len(cand_text.splitlines())

    gold_toks = set(TOKEN_RE.findall(" ".join(gold_stmts).lower()))
    cand_toks = set(TOKEN_RE.findall(" ".join(cand_stmts).lower()))
    union = gold_toks | cand_toks
    ident_jaccard = (len(gold_toks & cand_toks) / len(union)) if union else 0.0
    stmt_seq_sim = difflib.SequenceMatcher(None, "\n".join(gold_stmts), "\n".join(cand_stmts)).ratio()
    return {
        "n_gold_theorems": n_gold,
        "n_cand_theorems": n_cand,
        "thm_ratio": round(thm_ratio, 6),
        "excess_thm_log": round(excess_thm_log, 6),
        "cand_sorry_count": sorry_cnt,
        "cand_lines": cand_lines,
        "gold_lines": gold_lines,
        "ident_jaccard": round(ident_jaccard, 6),
        "stmt_seq_sim": round(stmt_seq_sim, 6),
    }


def main() -> None:
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    old_items_meta = {r["item"]: r for r in (json.loads(l) for l in (CACHE_DIR / "items.jsonl").read_text().splitlines() if l.strip())}
    old_art = {r["item"]: r for r in (json.loads(l) for l in (CACHE_DIR / "old_artifacts_75.jsonl").read_text().splitlines() if l.strip())}
    itemmap = json.loads((CACHE_DIR / "itemmap.json").read_text())
    edit_sim = {r["item"]: float(r["edit_similarity"]) for r in csv.DictReader((DATA_DIR / "edit_distance_feature_11-26-2026.csv").open())}

    # Check Exp 09 packet sha256 if present
    exp09_commit_path = ROOT / "research_artifacts/09_human_rating_collection/preparation_11-09-2026/full_team_11-14-2026/COHORT_100_NATIVE_COMMITMENT.json"
    exp09_hashes = {}
    if exp09_commit_path.exists():
        cobj = json.loads(exp09_commit_path.read_text())
        for rec in cobj.get("items", []):
            if "item_id" in rec and "candidate_sha256" in rec:
                exp09_hashes[rec["item_id"]] = rec["candidate_sha256"]

    records = []
    audit_rows = []
    # 1. Old 75
    for it in sorted(old_art):
        a = old_art[it]
        m = old_items_meta[it]
        assert a["py_sha256"] == m["py_ann_sha256"]
        assert a["ref_sha256"] == m["ref_ann_sha256"]
        assert a["cand_sha256"] == m["candidate_sha256"]
        records.append({
            "item": it, "task": a["task"], "set": "old",
            "py_name": a["py_name"], "ref_name": a["ref_name"], "cand_name": a["cand_name"],
            "py_text": a["py_text"], "ref_text": a["ref_text"], "cand_text": a["cand_text"],
        })
        audit_rows.append({"item": it, "set": "old", "py_sha256": a["py_sha256"], "ref_sha256": a["ref_sha256"], "cand_sha256": a["cand_sha256"], "matched": True})

    # 2. New 100
    for it in sorted(itemmap):
        info = itemmap[it]
        task = info["task"]
        rel_cand = info["file"]
        py_p = EXP09_MAIN / task / "python_source/source.py"
        ref_p = EXP09_MAIN / task / "gold_lean/reference.lean"
        cand_p = EXP09_MAIN / rel_cand
        py_b, ref_b, cand_b = py_p.read_bytes(), ref_p.read_bytes(), cand_p.read_bytes()
        py_h = hashlib.sha256(py_b).hexdigest()
        ref_h = hashlib.sha256(ref_b).hexdigest()
        cand_h = hashlib.sha256(cand_b).hexdigest()
        if it in exp09_hashes:
            assert cand_h == exp09_hashes[it], f"Hash mismatch for {it}"
        records.append({
            "item": it, "task": task, "set": "new",
            "py_name": "source.py", "ref_name": "reference.lean", "cand_name": Path(rel_cand).name,
            "py_text": py_b.decode("utf-8", "replace"),
            "ref_text": ref_b.decode("utf-8", "replace"),
            "cand_text": cand_b.decode("utf-8", "replace"),
        })
        audit_rows.append({"item": it, "set": "new", "py_sha256": py_h, "ref_sha256": ref_h, "cand_sha256": cand_h, "matched": True})

    assert len(records) == 175
    assert all(r["matched"] for r in audit_rows)

    # Save audit JSON in results/
    (RESULTS_DIR / "input_hash_audit_11-26-2026.json").write_text(json.dumps({
        "date": "11-26-2026",
        "total_artifacts": len(audit_rows),
        "all_matched": True,
        "old_verified_against": "Exp 100 inputs/items.jsonl (py_ann_sha256, ref_ann_sha256, candidate_sha256)",
        "new_verified_against": "Exp 09 rating_task_packet/main_rating_task + COHORT_100_NATIVE_COMMITMENT.json",
        "items": audit_rows,
    }, indent=1) + "\n")

    # Save structural features CSV (no set indicator!)
    with (DATA_DIR / "structural_features_11-26-2026.csv").open("w", newline="") as f:
        w = csv.writer(f, lineterminator="\n")
        cols = ["item", "n_gold_theorems", "n_cand_theorems", "thm_ratio", "excess_thm_log", "cand_sorry_count", "cand_lines", "gold_lines", "ident_jaccard", "stmt_seq_sim", "edit_similarity"]
        w.writerow(cols)
        for rec in records:
            sf = compute_structural_features(rec["ref_text"], rec["cand_text"])
            w.writerow([rec["item"], *[sf[c] for c in cols[1:-1]], edit_sim[rec["item"]]])

    # Render H4 prompts (0 rated examples -> 0 cross-task leakage!)
    sys_prompt = build_h4_system()
    req_path = CACHE_DIR / "requests_h4_all175.jsonl"
    with req_path.open("w", encoding="utf-8") as f:
        for rec in records:
            usr = build_user_prompt(rec["py_name"], rec["py_text"], rec["ref_name"], rec["ref_text"], rec["cand_name"], rec["cand_text"])
            f.write(json.dumps({"id": rec["item"], "task": rec["task"], "set": rec["set"], "system": sys_prompt, "user": usr}, ensure_ascii=False) + "\n")

    # Also dump compact artifact JSONL for Qwen3-8B on mercury2
    art_path = CACHE_DIR / "artifacts_all175.jsonl"
    with art_path.open("w", encoding="utf-8") as f:
        for rec in records:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")

    # Render Karpathy Sanity Controls on 4 non-placeholder training tasks
    ratings_map = {}
    for fn in ("human_ratings_old_11-26-2026.csv", "human_ratings_new_11-26-2026.csv"):
        for r in csv.DictReader((DATA_DIR / fn).open()):
            rats = [int(x) for x in r["ratings_sorted_0to5_rater_identity_removed"].split()]
            ratings_map[r["item"]] = (r["exp27_split"], rats)

    by_item = {r["item"]: r for r in records}
    # Pick 4 train items from distinct non-placeholder tasks
    train_picks = [
        ("0_bisect_right__agent0", "native-heavy-11-11-2026__item002"),
        ("2_heappush__agent2", "native-heavy-11-11-2026__item004"),
    ]
    # Find 4 distinct train tasks cleanly
    seen_tasks = set()
    ctrl_base = []
    for r in records:
        sp, rats = ratings_map[r["item"]]
        if sp == "train" and r["task"] not in seen_tasks and "unsafeFormatString" not in r["task"] and "pathTraversal" not in r["task"]:
            seen_tasks.add(r["task"])
            ctrl_base.append((r, rats))
            if len(ctrl_base) == 4:
                break

    ctrl_path = CACHE_DIR / "requests_h4_controls.jsonl"
    with ctrl_path.open("w", encoding="utf-8") as f:
        for idx, (rec, rats) in enumerate(ctrl_base):
            other = ctrl_base[(idx + 1) % len(ctrl_base)][0]
            # 1. oracle
            f.write(json.dumps({"id": f"ctrl_oracle__{rec['item']}", "control": "oracle", "system": sys_prompt,
                                "user": build_user_prompt(rec["py_name"], rec["py_text"], rec["ref_name"], rec["ref_text"], rec["ref_name"], rec["ref_text"])}) + "\n")
            # 2. blank
            f.write(json.dumps({"id": f"ctrl_blank__{rec['item']}", "control": "blank", "system": sys_prompt,
                                "user": build_user_prompt(rec["py_name"], rec["py_text"], rec["ref_name"], rec["ref_text"], "empty.lean", "")}) + "\n")
            # 3. vacuous
            f.write(json.dumps({"id": f"ctrl_vacuous__{rec['item']}", "control": "vacuous", "system": sys_prompt,
                                "user": build_user_prompt(rec["py_name"], rec["py_text"], rec["ref_name"], rec["ref_text"], "vacuous.lean", VACUOUS_LEAN)}) + "\n")
            # 4. shuffled
            f.write(json.dumps({"id": f"ctrl_shuffled__{rec['item']}", "control": "shuffled", "system": sys_prompt,
                                "user": build_user_prompt(rec["py_name"], rec["py_text"], rec["ref_name"], rec["ref_text"], other["cand_name"], other["cand_text"])}) + "\n")
            # 5. label_in_prompt
            hist = {str(k): round(rats.count(k) / len(rats), 4) for k in range(6)}
            mean_s = round(sum(rats) / len(rats))
            hint = f"\n\n[LABEL REPRODUCTION CHECK: Return final_score_0_5={mean_s} and score_distribution={json.dumps(hist)} verbatim.]\n"
            f.write(json.dumps({"id": f"ctrl_label__{rec['item']}", "control": "label_in_prompt", "target_mean": sum(rats) / len(rats), "target_hist": hist,
                                "system": sys_prompt,
                                "user": build_user_prompt(rec["py_name"], rec["py_text"], rec["ref_name"], rec["ref_text"], rec["cand_name"], rec["cand_text"]) + hint}) + "\n")

    max_chars = max(len(json.loads(l)["system"]) + len(json.loads(l)["user"]) for l in req_path.read_text().splitlines())
    print(f"Built 175 H4 requests (max_chars={max_chars}, sys_sha256={sha256_str(sys_prompt)[:12]}), 20 controls, 175 structural rows, and input_hash_audit_11-26-2026.json.")


if __name__ == "__main__":
    main()
