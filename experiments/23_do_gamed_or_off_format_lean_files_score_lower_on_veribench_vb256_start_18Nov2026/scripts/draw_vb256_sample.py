"""Draw the VB256 LLM sample and the targeted shadowing set by the rule pre-registered in README.md (11-19-2026).

Run after `gate.py vb256 --kernel-audit`; only the faithful gold rows of results/gate_vb256.csv are read (no
gaming-condition result and no judge score is an input).

- Eligible task: its faithful gold copy passes every check of the primary pipeline (`passes_all_checks`: compiles,
  kernel axiom audit clean, no `sorry` warning, no `axiom` declaration, no unsafe/implemented_by/extern, has
  Pre/Post/correctness, no vacuous-Prop flag, no name-shadowing flag).
- 30-task sample, stratified by split: EasySet 2, CSSet 2, HumanEval 2, RealCodeSet 2, SecuritySet 14, IndustrySet 8
  (at least 2 per split; the other 22 proportional to SecuritySet 136 : IndustrySet 79). A split with fewer eligible
  tasks gives all of them and its shortfall goes to SecuritySet and IndustrySet in the ratio 136 : 79 (largest
  remainder). One generator, random.Random(0), draws `sample(sorted(eligible ids), k)` per split in the order below.
- Targeted shadowing set: every eligible task whose comment-stripped gold uses the word Perm, Sorted or Pairwise;
  if more than 30, random.Random(1).sample(sorted(ids), 30).
"""
import csv, json, random
from common import V2, SHADOW_TARGET_NAMES
from gate import strip_comments
ORDER = ["easy_set", "cs_set", "humaneval_set", "realcode_set", "security_set", "industry_set"]
ALLOC = dict(easy_set=2, cs_set=2, humaneval_set=2, realcode_set=2, security_set=14, industry_set=8)

man_path = V2 / "inputs/vb256_manifest.json"; man = json.load(open(man_path))
split = {r["task"]: r["split"] for r in man["rows"]}
gate = {r["task"]: r for r in csv.DictReader(open(V2 / "results/gate_vb256.csv")) if r["condition"] == "faithful_gold_copy"}
assert set(gate) == set(split), "gold gate must cover all 256 tasks"
elig = {s: sorted(t for t in split if split[t] == s and gate[t]["passes_all_checks"] == "1") for s in ORDER}
alloc = dict(ALLOC); short = 0
for s in ORDER:  # deviation D1 (11-19-2026): the first version only handled the four small splits; the README's rule
    if len(elig[s]) < alloc[s]:  # moves any split's shortfall to SecuritySet and IndustrySet (136 : 79) where they have room
        short += alloc[s] - len(elig[s]); alloc[s] = len(elig[s])
while short > 0:
    room = [s for s in ("security_set", "industry_set") if len(elig[s]) > alloc[s]]
    if not room: break
    give = {room[0]: short} if len(room) == 1 else {"security_set": round(short * 136 / 215), "industry_set": short - round(short * 136 / 215)}
    for s, k in give.items():
        add = min(k, len(elig[s]) - alloc[s]); alloc[s] += add; short -= add
rng = random.Random(0); sample = []
for s in ORDER:
    k = min(alloc[s], len(elig[s])); sample += rng.sample(elig[s], k)
targets = sorted(t for s in ORDER for t in elig[s]
                 if SHADOW_TARGET_NAMES.search(strip_comments((V2 / "inputs/vb256" / t / "gold.lean").read_text())))
if len(targets) > 30:
    targets = sorted(random.Random(1).sample(targets, 30))
# Exploratory IndustrySet extension (added 11-19-2026 after the gold check showed 75 of 79 IndustrySet references
# depending on native_decide; not part of the primary analysis): 4 IndustrySet tasks whose faithful gold fails the
# kernel gate only through Lean.ofReduceBool and passes every other check; random.Random(2).sample(sorted(ids), 4).
nd_only = sorted(t for t in split if split[t] == "industry_set" and gate[t]["compiles"] == "1" and gate[t]["audit_ran"] == "1"
                 and gate[t]["bad_axioms"] == "Lean.ofReduceBool" and gate[t]["sorry_warning"] == "0" and gate[t]["declares_axiom_code"] == "0"
                 and gate[t]["unsafe_or_implemented_by"] == "0" and gate[t]["has_pre_post_correctness"] == "1"
                 and gate[t]["vacuous_prop_flag"] == "0" and gate[t]["shadow_flag"] == "0")
industry_ext = sorted(random.Random(2).sample(nd_only, 4))
man.update(eligible_counts={s: len(elig[s]) for s in ORDER}, allocation=alloc, llm_sample=sorted(sample),
           shadow_target_tasks=targets, industry_extension=industry_ext, industry_extension_pool=len(nd_only),
           sample_rule="draw_vb256_sample.py: faithful gold passes all primary checks; stratified 2/2/2/2/14/8 by split; random.Random(0)")
json.dump(man, open(man_path, "w"), indent=1)
print("eligible per split:", man["eligible_counts"]); print("allocation:", alloc)
print("sample:", len(sample)); print("shadow targets:", len(targets)); print("IndustrySet extension:", industry_ext, "from", len(nd_only))
