# TC Human Rating Prompt (Simplified)

Please rate how well the **agent Lean theorem statements** cover the **gold Lean theorem statements**.

You have 3 files per problem:

1. Python source
2. Gold Lean file
3. Agent Lean file

## Scope

- Judge **statement coverage only** (not proof style or proof quality).
- A gold theorem is “covered” if the agent has:
  - the same theorem, or
  - a logically equivalent theorem, or
  - a stronger theorem implying the gold theorem, or
  - a small set of lemmas that clearly recovers the gold theorem.

## Quick checklist

- **A**: Are key gold theorems covered? (Y/N)
- **B**: Are gold pre/postconditions preserved or strengthened? (Y/N)
- **C**: Is there obvious theorem spam? (Y/N)
- **D**: If spam exists, is it a **handful** or does it **dominate**?

## Base score (before spam adjustment)

- **5** = all gold guarantees covered
- **4** = mostly covered; only 1–2 minor gaps
- **3** = partial; at least one important gap
- **2** = weak; only a few gold theorems covered (< half)
- **1** = no gold theorem covered, but at least one non-vacuous relevant theorem
- **0** = vacuous/broken; no meaningful relevant theorem coverage

## Spam adjustment

- If **C=No**: no change
- If **C=Yes** and **D=handful**: lower by up to 1
- If **C=Yes** and **D=dominates**: lower by up to 2

## Output format (required)

Make a copy of the [rater sheet](https://docs.google.com/spreadsheets/d/1IhyiTVKYEQg4wVSXxaGZiCwEd-IFvg5S2nv3XD3cNXM/edit?gid=0#gid=0) with your name and fill in the score columns.

Optional notes to include if you have time:

A: [Y/N] B: [Y/N] C: [Y/N] D: [handful/dominates/N/A]  
Score: [0-5] Confidence: [Low/Med/High]  
Rationale: [2–4 sentences: name >=1 covered and >=1 uncovered gold theorem if any; include spam examples if C=Yes]

## Tie-break rule

If unsure between two adjacent scores, choose the lower one unless you can clearly justify the higher one.
