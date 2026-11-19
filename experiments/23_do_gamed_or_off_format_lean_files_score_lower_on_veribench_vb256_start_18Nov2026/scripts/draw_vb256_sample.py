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
for s in ORDER[:4]:
    if len(elig[s]) < alloc[s]:
        short += alloc[s] - len(elig[s]); alloc[s] = len(elig[s])
if short:
    sec = round(short * 136 / 215); alloc["security_set"] += sec; alloc["industry_set"] += short - sec
rng = random.Random(0); sample = []
for s in ORDER:
    k = min(alloc[s], len(elig[s])); sample += rng.sample(elig[s], k)
targets = sorted(t for s in ORDER for t in elig[s]
                 if SHADOW_TARGET_NAMES.search(strip_comments((V2 / "inputs/vb256" / t / "gold.lean").read_text())))
if len(targets) > 30:
    targets = sorted(random.Random(1).sample(targets, 30))
man.update(eligible_counts={s: len(elig[s]) for s in ORDER}, allocation=alloc, llm_sample=sorted(sample),
           shadow_target_tasks=targets,
           sample_rule="draw_vb256_sample.py: faithful gold passes all primary checks; stratified 2/2/2/2/14/8 by split; random.Random(0)")
json.dump(man, open(man_path, "w"), indent=1)
print("eligible per split:", man["eligible_counts"]); print("allocation:", alloc)
print("sample:", len(sample)); print("shadow targets:", len(targets))
