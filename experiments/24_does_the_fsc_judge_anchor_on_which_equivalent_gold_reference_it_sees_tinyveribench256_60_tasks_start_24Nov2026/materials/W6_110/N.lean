import Mathlib
namespace Agent

/-!
# Unsafe BPF packet-read permission check

Translation of the Python `unsafe_bpf_oob_read` example from symbolic execution.
The function returns a permission flag, not packet contents: it tests only
`offset < pkt_len`, ignoring `length`. In particular, it neither checks the
lower bound on the offset nor checks `offset + length <= pkt_len`.

All arguments are `Int`, preserving Python's arbitrary-precision signed integer
domain without adding machine overflow or implicit nonnegativity assumptions.
The specification describes the vulnerable program, not a repaired filter.
The Boolean `check` encodes the six assertions in the Python test harness.
-/

namespace UnsafeBpfOobRead

/-! ## Functional implementation -/

/-- Deliberately unsafe: only the starting offset is compared to the packet size. -/
def unsafe_bpf_oob_read (offset : Int) (_length : Int) (pkt_len : Int) : Bool :=
  if offset < pkt_len then true else false

/-- Boolean counterpart of the Python assertion harness. -/
def check (candidate : Int → Int → Int → Bool) : Bool :=
  (candidate 0 4 20 == true) &&
  (candidate 18 4 20 == true) &&
  (candidate 20 4 20 == false) &&
  (candidate 0 100 20 == true) &&
  (candidate 5 0 20 == true) &&
  (candidate 19 2 20 == true)

/-! ## Unit tests: all six original assertions -/

example : unsafe_bpf_oob_read 0 4 20 = true := by native_decide
example : unsafe_bpf_oob_read 18 4 20 = true := by native_decide
example : unsafe_bpf_oob_read 20 4 20 = false := by native_decide
example : unsafe_bpf_oob_read 0 100 20 = true := by native_decide
example : unsafe_bpf_oob_read 5 0 20 = true := by native_decide
example : unsafe_bpf_oob_read 19 2 20 = true := by native_decide
example : check unsafe_bpf_oob_read = true := by native_decide

#eval check unsafe_bpf_oob_read
#eval if check unsafe_bpf_oob_read then "All tests passed." else "Candidate failed tests"

-- Extra boundary tests document the full signed domain, including zero lengths
-- at a rejected start offset. These are not restrictions on the specification.
example : unsafe_bpf_oob_read (-1) 4 20 = true := by native_decide
example : unsafe_bpf_oob_read (-3) 8 (-1) = true := by native_decide
example : unsafe_bpf_oob_read 18 (-100) 20 = true := by native_decide
example : unsafe_bpf_oob_read 20 0 20 = false := by native_decide
example : unsafe_bpf_oob_read 0 0 0 = false := by native_decide

/-! ## Precondition -/

/-- Python accepts every integer triple; no extra assumptions are imposed. -/
def Pre (_offset _length _pkt_len : Int) : Prop := True

/-! ## Properties and kernel-checked proofs -/

/-- Exact characterization of permission. -/
def allow_prop (offset length pkt_len : Int) : Prop :=
  unsafe_bpf_oob_read offset length pkt_len = true ↔ offset < pkt_len

theorem allow_thm (offset length pkt_len : Int) : allow_prop offset length pkt_len := by sorry

/-- The starting offset alone also exactly characterizes rejection. -/
def reject_prop (offset length pkt_len : Int) : Prop :=
  unsafe_bpf_oob_read offset length pkt_len = false ↔ pkt_len ≤ offset

theorem reject_thm (offset length pkt_len : Int) : reject_prop offset length pkt_len := by sorry

/-- Changing the requested length cannot change the result, even for negative lengths. -/
def length_ignored_prop (offset length pkt_len : Int) : Prop :=
  ∀ otherLength : Int,
    unsafe_bpf_oob_read offset length pkt_len =
      unsafe_bpf_oob_read offset otherLength pkt_len

theorem length_ignored_thm (offset length pkt_len : Int) :
    length_ignored_prop offset length pkt_len := by sorry

/-- Ordinary in-bounds reads with an in-range start are permitted.
The strict start condition is necessary even when the requested length is zero. -/
def safe_read_prop (offset length pkt_len : Int) : Prop :=
  (0 ≤ offset ∧ 0 ≤ length ∧ offset < pkt_len ∧ offset + length ≤ pkt_len) →
    unsafe_bpf_oob_read offset length pkt_len = true

theorem safe_read_thm (offset length pkt_len : Int) :
    safe_read_prop offset length pkt_len := by sorry

/-- Exact characterization of permitted reads whose end exceeds the packet.
This describes the upper-bound vulnerability, not a safety guarantee. -/
def past_end_prop (offset length pkt_len : Int) : Prop :=
  (unsafe_bpf_oob_read offset length pkt_len = true ∧ pkt_len < offset + length) ↔
    (offset < pkt_len ∧ pkt_len < offset + length)

theorem past_end_thm (offset length pkt_len : Int) :
    past_end_prop offset length pkt_len := by sorry

/-- The Python function does not even reject negative offsets in nonnegative packets. -/
def negative_start_prop (offset length pkt_len : Int) : Prop :=
  offset < 0 → 0 ≤ pkt_len → unsafe_bpf_oob_read offset length pkt_len = true

theorem negative_start_thm (offset length pkt_len : Int) :
    negative_start_prop offset length pkt_len := by sorry

/-- Every positive packet size admits a concrete positive-length overrun:
read two bytes from the last valid (nonnegative) starting offset. -/
def overrun_witness_prop (pkt_len : Int) : Prop :=
  0 < pkt_len →
    (0 ≤ pkt_len - 1 ∧
     unsafe_bpf_oob_read (pkt_len - 1) 2 pkt_len = true ∧
     pkt_len < (pkt_len - 1) + 2)

theorem overrun_witness_thm (pkt_len : Int) : overrun_witness_prop pkt_len := by sorry

/-! ## Postcondition -/

/-- Behavioral correctness of the unsafe implementation is not memory safety. -/
def Post_prop (offset length pkt_len : Int) : Prop :=
  allow_prop offset length pkt_len ∧
  reject_prop offset length pkt_len ∧
  length_ignored_prop offset length pkt_len ∧
  safe_read_prop offset length pkt_len ∧
  past_end_prop offset length pkt_len ∧
  negative_start_prop offset length pkt_len ∧
  overrun_witness_prop pkt_len

/-! ## Property-based tests

These exhaustive finite PBTs exercise signed values, zero, small values, the
original packet boundary, and large positive/negative lengths. The bounds apply
only to tests, not to theorem statements or `Pre`. Each check below is an
executable form of the named property, independent of any Decidable instance
for the specification definitions. For universal length independence, the fourth
test argument instantiates `otherLength`; the post-condition PBT does the same.
-/

def pbtInts : List Int :=
  (List.range 13).map (fun n => (n : Int) - 4) ++ [18, 19, 20, 21, 100, -100]

def testTriples (p : Int → Int → Int → Bool) : Bool :=
  pbtInts.all fun offset =>
    pbtInts.all fun length =>
      pbtInts.all fun pkt_len => p offset length pkt_len

def testQuads (p : Int → Int → Int → Int → Bool) : Bool :=
  pbtInts.all fun offset =>
    pbtInts.all fun length =>
      pbtInts.all fun pkt_len =>
        pbtInts.all fun otherLength => p offset length pkt_len otherLength

-- PBT for allow_prop.
def allowPbt : Bool := testTriples fun offset length pkt_len =>
  decide (unsafe_bpf_oob_read offset length pkt_len = true ↔ offset < pkt_len)
example : allowPbt = true := by native_decide
#eval allowPbt

-- PBT for reject_prop.
def rejectPbt : Bool := testTriples fun offset length pkt_len =>
  decide (unsafe_bpf_oob_read offset length pkt_len = false ↔ pkt_len ≤ offset)
example : rejectPbt = true := by native_decide
#eval rejectPbt

-- PBT for length_ignored_prop, including many pairs of different lengths.
def lengthIgnoredPbt : Bool := testQuads fun offset length pkt_len otherLength =>
  unsafe_bpf_oob_read offset length pkt_len ==
    unsafe_bpf_oob_read offset otherLength pkt_len
example : lengthIgnoredPbt = true := by native_decide
#eval lengthIgnoredPbt

-- PBT for safe_read_prop.
def safeReadPbt : Bool := testTriples fun offset length pkt_len =>
  decide ((0 ≤ offset ∧ 0 ≤ length ∧ offset < pkt_len ∧ offset + length ≤ pkt_len) →
    unsafe_bpf_oob_read offset length pkt_len = true)
example : safeReadPbt = true := by native_decide
#eval safeReadPbt

-- PBT for past_end_prop, with both overrunning and non-overrunning reads.
def pastEndPbt : Bool := testTriples fun offset length pkt_len =>
  decide ((unsafe_bpf_oob_read offset length pkt_len = true ∧ pkt_len < offset + length) ↔
    (offset < pkt_len ∧ pkt_len < offset + length))
example : pastEndPbt = true := by native_decide
#eval pastEndPbt

-- PBT for negative_start_prop.
def negativeStartPbt : Bool := testTriples fun offset length pkt_len =>
  decide (offset < 0 → 0 ≤ pkt_len → unsafe_bpf_oob_read offset length pkt_len = true)
example : negativeStartPbt = true := by native_decide
#eval negativeStartPbt

-- PBT for overrun_witness_prop.
def overrunWitnessPbt : Bool := pbtInts.all fun pkt_len =>
  decide (0 < pkt_len →
    (0 ≤ pkt_len - 1 ∧
     unsafe_bpf_oob_read (pkt_len - 1) 2 pkt_len = true ∧
     pkt_len < (pkt_len - 1) + 2))
example : overrunWitnessPbt = true := by native_decide
#eval overrunWitnessPbt

-- PBT for the entire Post_prop; Pre is True for every tested input.
def postPbt : Bool := testQuads fun offset length pkt_len otherLength =>
  decide (
    (unsafe_bpf_oob_read offset length pkt_len = true ↔ offset < pkt_len) ∧
    (unsafe_bpf_oob_read offset length pkt_len = false ↔ pkt_len ≤ offset) ∧
    (unsafe_bpf_oob_read offset length pkt_len =
      unsafe_bpf_oob_read offset otherLength pkt_len) ∧
    ((0 ≤ offset ∧ 0 ≤ length ∧ offset < pkt_len ∧ offset + length ≤ pkt_len) →
      unsafe_bpf_oob_read offset length pkt_len = true) ∧
    ((unsafe_bpf_oob_read offset length pkt_len = true ∧ pkt_len < offset + length) ↔
      (offset < pkt_len ∧ pkt_len < offset + length)) ∧
    (offset < 0 → 0 ≤ pkt_len → unsafe_bpf_oob_read offset length pkt_len = true) ∧
    (0 < pkt_len →
      (0 ≤ pkt_len - 1 ∧
       unsafe_bpf_oob_read (pkt_len - 1) 2 pkt_len = true ∧
       pkt_len < (pkt_len - 1) + 2)))
example : postPbt = true := by native_decide
#eval postPbt

/-! ## Correctness: the program satisfies the behavioral postcondition -/

theorem correctness_thm (offset length pkt_len : Int) :
    Pre offset length pkt_len → Post_prop offset length pkt_len := by sorry

/-! ## Imperative implementation -/

/-- Mutable permission flag, preserving the same single, incomplete range check. -/
def unsafe_bpf_oob_read_imp (offset : Int) (_length : Int) (pkt_len : Int) : Bool :=
  Id.run do
    let mut permitted := false
    if offset < pkt_len then
      permitted := true
    return permitted

/-! ## Imperative tests -/

example : unsafe_bpf_oob_read_imp 0 4 20 = true := by native_decide
example : unsafe_bpf_oob_read_imp 18 4 20 = true := by native_decide
example : unsafe_bpf_oob_read_imp 20 4 20 = false := by native_decide
example : unsafe_bpf_oob_read_imp 0 100 20 = true := by native_decide
example : unsafe_bpf_oob_read_imp 5 0 20 = true := by native_decide
example : unsafe_bpf_oob_read_imp 19 2 20 = true := by native_decide
example : check unsafe_bpf_oob_read_imp = true := by native_decide
#eval check unsafe_bpf_oob_read_imp
#eval if check unsafe_bpf_oob_read_imp then "All tests passed." else "Candidate failed tests"

-- Bounded PBT of equivalence, in addition to the universal proof below.
example : testTriples (fun offset length pkt_len =>
    unsafe_bpf_oob_read offset length pkt_len ==
      unsafe_bpf_oob_read_imp offset length pkt_len) = true := by native_decide

/-! ## Functional / imperative equivalence -/

theorem equivalence_thm (offset length pkt_len : Int) :
    unsafe_bpf_oob_read offset length pkt_len =
      unsafe_bpf_oob_read_imp offset length pkt_len := by sorry

end UnsafeBpfOobRead
end Agent
