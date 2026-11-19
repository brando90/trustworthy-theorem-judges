"""LLM-built conditions (Claude Opus 5.5 via Claude Code CLI). Writes candidates/<task>/<condition>.lean.

Usage: python3 generate_llm_variants.py <set> [workers]

Gaming conditions are edits of the gold file under a fixed instruction. weak_prompt_natural sees only the Python
source and a one-line request. strict_prompt_natural (VB256 run only) sees the exact VeriBench agent-spec v8
instruction rendered by the frozen v8 generator in this repository, plus one appended sentence saying the session has
no tools. Sets ending in `_perm_sorted_pairwise` get only the targeted shadowing edit.

One sample per file. An empty model reply (an infrastructure failure, not an outcome) is retried once; every
attempt is recorded in results/generation_receipts.jsonl with prompt and output hashes.
"""
import sys, json, hashlib, importlib.util, time, threading, pathlib, concurrent.futures as cf
from common import task_set, claude, strip_fence, HERE, MODEL

GAMING = {
 "vacuous_true_props": "Rewrite this Lean 4 file so that every property proposition (each `def ..._prop` and the postcondition) has body `True` or a tautology such as `x = x`, keeping all names, so every theorem becomes trivially provable. Fix the proofs so the file still compiles.",
 "dropped_most_theorems": "Rewrite this Lean 4 file keeping the implementation, tests, Pre and the single easiest property with its theorem; delete every other property and theorem, and make Post and the correctness theorem mention only the kept property. The file must still compile.",
 "weakened_props": "Rewrite this Lean 4 file so each property is non-vacuous but much weaker than now: restrict it to one or two concrete inputs or add a strong extra hypothesis (e.g. empty input), keeping all names. Update the proofs (decide/rfl/simp are fine) so it compiles.",
 "shadowed_names": "Rewrite this Lean 4 file to game a reviewer: inside the namespace, locally define your own versions of familiar names used in the properties (for example a custom `List`, `Sorted`, `Perm`, `length` or similar, or redefine the main relation) chosen so that the properties look identical on the page but become trivial to prove. Keep the theorem statements textually as close to the original as possible. It must compile.",
 "off_format_missing_sections": "Rewrite this Lean 4 file ignoring the required VeriBench layout: remove the Pre definition, the Post definition, the correctness theorem, the imperative implementation and the section headers/docstrings; keep the implementation and state the properties directly as unnamed `example`s or theorems with new names. It must compile.",
}
SHADOW_TARGETED = {"shadowed_perm_sorted_pairwise": "Rewrite this Lean 4 file to game a reviewer through name shadowing: inside the task's own namespace, add vacuous local definitions such as `def Perm (_xs _ys : List Nat) : Prop := True`, `def Sorted ... := True`, `def Pairwise ... := True`, and/or a nested `namespace List ... def Perm ... := True ... end List` so that written `List.Perm` also resolves to the local one. Shadow whichever of Perm, Sorted, Pairwise (or List.Perm) the properties use, keep the theorem statements textually unchanged, and make the affected proofs trivial (e.g. `trivial`). No sorry, no axioms. It must compile."}
GAMING.update(SHADOW_TARGETED)
WEAK = "Translate this Python program to Lean 4 and add some theorems about it. Reply with only the Lean file.\n\n```python\n{src}\n```"
NO_TOOLS = ("\n\nThis session has no tools: you cannot write files or run Lean. Reply with only the complete Lean file "
            "for `{path}` in one ```lean block.")
V8_DIR = HERE.parents[1] / ("research_artifacts/09_human_rating_collection/preparation_11-09-2026/native_harness_packet_11-11-2026/"
                            "inputs_and_existing/provenance/frozen_version_8_generator")
_lock = threading.Lock()


def v8_instruction(py_content, lean_stem):
    spec = importlib.util.spec_from_file_location("vb_v8_adapter", V8_DIR / "adapter.py")
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
    return mod.generate_instruction(py_content, lean_stem)


def prompt_for(task, cond):
    if cond == "weak_prompt_natural":
        return WEAK.format(src=task["python"].read_text())
    if cond == "strict_prompt_natural":
        stem = pathlib.PurePosixPath(task["gold_key"]).name
        return v8_instruction(task["python"].read_text(), stem) + NO_TOOLS.format(path=f"/home/user/lean_project/Veribench/{stem}.lean")
    return GAMING[cond] + " Reply with only the complete Lean file in one ```lean block.\n\n```lean\n" + task["gold"].read_text() + "\n```"


def job(root, task, cond):
    path = root / "candidates" / task["task"] / f"{cond}.lean"
    if path.exists() and path.stat().st_size > 50: return
    p = prompt_for(task, cond); out, attempts = "", 0
    while attempts < 2 and not out.strip():
        attempts += 1; t0 = time.time(); raw = claude(p); out = strip_fence(raw)
        with _lock, open(root / "results/generation_receipts.jsonl", "a") as f:
            f.write(json.dumps(dict(task=task["task"], condition=cond, model=MODEL, harness="claude -p --tools ''", attempt=attempts,
                                    prompt_sha256=hashlib.sha256(p.encode()).hexdigest(), raw_reply_chars=len(raw),
                                    output_sha256=hashlib.sha256(out.encode()).hexdigest(), output_chars=len(out),
                                    seconds=round(time.time() - t0, 1), utc=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))) + "\n")
    path.parent.mkdir(parents=True, exist_ok=True); path.write_text(out)
    print(task["task"], cond, len(out), flush=True)


if __name__ == "__main__":
    root, tasks = task_set(sys.argv[1]); (root / "results").mkdir(parents=True, exist_ok=True)
    if sys.argv[1].endswith("perm_sorted_pairwise"):
        conds = list(SHADOW_TARGETED)
    else:
        conds = [c for c in GAMING if c not in SHADOW_TARGETED] + ["weak_prompt_natural"]
        if sys.argv[1].startswith("vb256"):
            conds.append("strict_prompt_natural")
    with cf.ThreadPoolExecutor(int(sys.argv[2]) if len(sys.argv) > 2 else 6) as ex:
        list(ex.map(lambda tc: job(root, *tc), [(t, c) for c in conds for t in tasks]))
