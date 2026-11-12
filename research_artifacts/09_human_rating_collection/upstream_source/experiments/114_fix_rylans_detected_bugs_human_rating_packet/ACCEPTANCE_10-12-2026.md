<!-- TLDR: Acceptance record for experiment 102's warm-up and set-N packet references after experiment 114's corrections: 27/27 references compile, have no sorry and use only standard axioms; every change was produced by one model family and reviewed by the other. -->
# Packet reference acceptance (10-12-2026)

**Decision:** both packets of experiment 102 (`warmup`, `setN`) are released with the corrected references below. Brando asked on 10-11-2026 that the packets contain no errors or false theorems and be ready for everyone to rate.

**Rule applied (Brando, 10-11-2026).** A reference is corrected when it is incorrect: a false theorem or test, or a contradiction with the Python on an input the Python accepts. A reasonable convention for inputs the Python rejects (empty lists, zero denominators) is kept and stated in a docstring. Abstractions that state nothing false (N20's flag model; `Nat` for Python `int`) are kept.

## Deterministic gate

`scripts/verify_corrected_references.py` (Lean 4.22.0 via `lake env lean`; originals read from git `290c90de20`):
- 27/27 references compile with exit 0 and 0 errors;
- 0 `sorry`/`admit` tokens anywhere;
- 1214 theorems (all theorems each module adds, private and auxiliary ones included) depend only on `propext`, `Classical.choice`, `Quot.sound`; `native_decide` appears only in `example` tests.
Full output: [results/verification.json](results/verification.json).

Python differential checks (every Lean test input plus extra accepted inputs) are in each folder's `corrected_references/<ID>/RECEIPT.md`; after the fixes no reference contradicts its Python on a tested accepted input.

## Per-reference record

| Folder | Verifier | Theorems axiom-checked | Producer | Cross-family review | Change |
|---|---|---:|---|---|---|
| W01 | PASS | 101 | Claude | Codex | proofs added; Float tests use `==`; `medianImp` quicksort comparator `≤`→`<` (real duplicate-order bug); empty-list convention stated; Python docstring 15.0→8.0 |
| W02 | PASS | 27 | Claude | Codex | **false theorem fixed**: `maximality_prop` now `d ∣ a → d ∣ b → d ∣ gcd a b` (old `≤` form false at (0,0)); `gcdImp` `while`→bounded loop (same results); proofs added |
| N01 | PASS | 7 | Claude | Codex | proofs added |
| N02 | PASS | 48 | Claude | Codex | proofs added; `isPrimeImp` `while`→bounded loop (same results) |
| N03 | PASS | 9 | original | Codex | none (already fully proved); differential checked |
| N04 | PASS | 8 | Claude | Codex | proofs added; docstring wording |
| N05 | PASS | 20 | Claude | Codex | proofs added; docstring wording |
| N06 | PASS | 10 | Claude | Codex | proofs added; docstring wording |
| N07 | PASS | 22 | Claude | Codex | proofs added; docstring wording |
| N08 | PASS | 62 | Claude + Codex | Codex / Claude | 3 theorems re-proved without `native_decide`; **Python order mismatch fixed**: candidate orders tried lexicographically (512/512 three-vertex graphs match Python, was 507/512); regression test added |
| N09 | PASS | 39 | Codex | Claude | proofs added; **3 false properties fixed** with hypothesis `primeFib n ≠ 0` (bounded search returns 0 when exhausted; false for n ≥ 10001) |
| N10 | PASS | 48 | Codex | Claude | proofs added; `b32encode_imp` `while`→bounded loop (same results); length docstring corrected |
| N11 | PASS | 39 | Claude | Codex | proofs added; `contains_all_numbers_prop` restated from opaque `containsSubstr` to an explicit substring (same meaning) |
| N12 | PASS | 64 | original | Codex | none (already fully proved); differential checked |
| N13 | PASS | 22 | Claude | Codex | equivalence proof repaired (did not compile) |
| N14 | PASS | 23 | Claude | Codex | proofs added |
| N15 | PASS | 33 | Claude | Codex | proofs added; `mySumDigitsImp` `while`→bounded loop (same results) |
| N16 | PASS | 10 | Claude | Codex | proofs added; empty-list convention stated |
| N17 | PASS | 230 | original | Codex | packaged the two imported reference files in `gold_lean_dependencies/` |
| N18 | PASS | 19 | Claude | Codex | equivalence proof repaired (did not compile) |
| N19 | PASS | 9 | Claude | Codex | proof switched from `native_decide` to `decide` |
| N20 | PASS | 9 | Claude | Codex | proofs added; note: hash check is abstracted as a flag (kept; not false) |
| N21 | PASS | 103 | original | Codex | none (already fully proved); differential checked |
| N22 | PASS | 20 | Claude | Codex | proofs added; **Python mismatch fixed**: `,` added to safe characters (Python returned `a,b`, Lean quoted it) |
| N23 | PASS | 97 | Codex + Claude | Claude / Codex | proofs added; **2 false invariance properties fixed** (custom rationals with zero denominator); **imperative bug fixed** (duplicates sorted wrongly; now same merge sort as functional + Python input check); equivalence proved |
| N24 | PASS | 100 | Claude | Codex | proofs added; `median_lowImp` quicksort comparator `≤`→`<` (real duplicate-order bug) |
| N25 | PASS | 35 | original | Codex | none (already fully proved); differential checked |

Producers: Claude Code (Claude Opus 5.5 subagents) and Codex CLI (`gpt-6-astra`, high reasoning). Each change was reviewed by the other family; reviews are appended to the receipts. Agent Lean files, the scoring instructions (`human_judgements_prompt.md`, SHA-256 `b29e9caf…`) and the sealed keys are unchanged.

## Warm-up answer key

The warm-up's sealed key (`742ecc70…`) was rated by May experts on the old W02 reference. W02's maximality theorem changed; W02a states maximality in the same divisibility form, so its target score may rise. Brando should re-check the W02a key item before warm-up scores are used for qualification.
