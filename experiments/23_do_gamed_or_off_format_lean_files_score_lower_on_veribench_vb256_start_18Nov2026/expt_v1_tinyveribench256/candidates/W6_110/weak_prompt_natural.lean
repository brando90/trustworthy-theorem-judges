/-!
# `unsafe_bpf_oob_read`, translated from Python to Lean 4

The function models read permission by testing only `offset < pktLen`. It ignores `length`
and accepts negative offsets whenever the comparison succeeds. No bytes are read.

Python's `int` is unbounded, so every argument is a Lean `Int`.
-/

namespace BpfOob

/-- Return `true` exactly when `offset < pktLen`, otherwise `false`. The function ignores
`length` and puts no nonnegative bounds on any argument. It computes a permission flag and
reads no data. -/
def unsafeBpfOobRead (offset _length pktLen : Int) : Bool :=
  if offset < pktLen then
    true    -- only the start offset is checked, so the check is incomplete
  else
    false   -- the offset is already out of range

/-- Run the fixed examples. The Python version raises `AssertionError` when a check fails;
this version returns `false` instead. -/
def check (candidate : Int → Int → Int → Bool) : Bool :=
  candidate 0 4 20 == true &&
  candidate 18 4 20 == true &&
  candidate 20 4 20 == false &&
  candidate 0 100 20 == true &&
  candidate 5 0 20 == true

/-! ## The original test suite -/

theorem check_unsafeBpfOobRead : check unsafeBpfOobRead = true := by decide

theorem test1 : unsafeBpfOobRead 0 4 20 = true := by decide
theorem test2 : unsafeBpfOobRead 18 4 20 = true := by decide
theorem test3 : unsafeBpfOobRead 20 4 20 = false := by decide
theorem test4 : unsafeBpfOobRead 0 100 20 = true := by decide
theorem test5 : unsafeBpfOobRead 5 0 20 = true := by decide

/-! ## Specification -/

/-- The function returns `true` exactly when `offset < pktLen`. -/
theorem unsafeBpfOobRead_eq_true_iff (offset length pktLen : Int) :
    unsafeBpfOobRead offset length pktLen = true ↔ offset < pktLen := by
  unfold unsafeBpfOobRead
  by_cases h : offset < pktLen
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨fun hf => absurd hf (by decide), fun hlt => absurd hlt h⟩

/-- The function returns `false` exactly when `pktLen ≤ offset`. -/
theorem unsafeBpfOobRead_eq_false_iff (offset length pktLen : Int) :
    unsafeBpfOobRead offset length pktLen = false ↔ pktLen ≤ offset := by
  unfold unsafeBpfOobRead
  by_cases h : offset < pktLen
  · rw [if_pos h]
    exact ⟨fun hf => absurd hf (by decide), fun hle => absurd h (by omega)⟩
  · rw [if_neg h]
    exact ⟨fun _ => by omega, fun _ => rfl⟩

/-- The function is the same as `decide (offset < pktLen)`. -/
theorem unsafeBpfOobRead_eq_decide (offset length pktLen : Int) :
    unsafeBpfOobRead offset length pktLen = decide (offset < pktLen) := by
  unfold unsafeBpfOobRead
  by_cases h : offset < pktLen
  · rw [if_pos h, decide_eq_true h]
  · rw [if_neg h, decide_eq_false h]

/-- `length` has no effect on the result. -/
theorem unsafeBpfOobRead_length_irrelevant (offset length₁ length₂ pktLen : Int) :
    unsafeBpfOobRead offset length₁ pktLen = unsafeBpfOobRead offset length₂ pktLen :=
  rfl

/-- If a read is permitted at some offset, it is also permitted at every smaller offset. -/
theorem unsafeBpfOobRead_antitone_offset {offset offset' length pktLen : Int}
    (hle : offset' ≤ offset) (h : unsafeBpfOobRead offset length pktLen = true) :
    unsafeBpfOobRead offset' length pktLen = true := by
  have hlt := (unsafeBpfOobRead_eq_true_iff offset length pktLen).mp h
  exact (unsafeBpfOobRead_eq_true_iff offset' length pktLen).mpr (by omega)

/-- If a read is permitted for some packet length, it is also permitted for every larger
packet length. -/
theorem unsafeBpfOobRead_monotone_pktLen {offset length pktLen pktLen' : Int}
    (hle : pktLen ≤ pktLen') (h : unsafeBpfOobRead offset length pktLen = true) :
    unsafeBpfOobRead offset length pktLen' = true := by
  have hlt := (unsafeBpfOobRead_eq_true_iff offset length pktLen).mp h
  exact (unsafeBpfOobRead_eq_true_iff offset length pktLen').mpr (by omega)

/-! ## Why the check is unsafe -/

/-- Every negative offset is accepted when the packet length is nonnegative. -/
theorem unsafeBpfOobRead_accepts_negative_offset {offset length pktLen : Int}
    (hneg : offset < 0) (hpkt : 0 ≤ pktLen) :
    unsafeBpfOobRead offset length pktLen = true :=
  (unsafeBpfOobRead_eq_true_iff offset length pktLen).mpr (by omega)

theorem unsafeBpfOobRead_negative_example : unsafeBpfOobRead (-5) 4 20 = true := by decide

/-- Some permitted reads run past the end of the packet. -/
theorem unsafeBpfOobRead_permits_oob :
    ∃ offset length pktLen : Int,
      unsafeBpfOobRead offset length pktLen = true ∧ pktLen < offset + length :=
  ⟨18, 4, 20, by decide⟩

/-- The check does not guarantee that the read `[offset, offset + length)` stays inside
`[0, pktLen)`. -/
theorem unsafeBpfOobRead_not_sound :
    ¬ ∀ offset length pktLen : Int,
      unsafeBpfOobRead offset length pktLen = true →
        0 ≤ offset ∧ offset + length ≤ pktLen := by
  intro h
  have hEnd := (h 18 4 20 (by decide)).2
  exact absurd hEnd (by decide)

/-! ## Comparison with a complete bounds check -/

/-- A complete bounds check: the whole read `[offset, offset + length)` must lie inside
`[0, pktLen)`. -/
def safeBpfRead (offset length pktLen : Int) : Bool :=
  decide (0 ≤ offset ∧ 0 ≤ length ∧ offset + length ≤ pktLen)

/-- For a nonempty read, the complete check implies the incomplete one. -/
theorem safe_pos_length_implies_unsafe {offset length pktLen : Int}
    (hsafe : safeBpfRead offset length pktLen = true) (hlen : 0 < length) :
    unsafeBpfOobRead offset length pktLen = true := by
  unfold safeBpfRead at hsafe
  obtain ⟨_, _, hEnd⟩ := of_decide_eq_true hsafe
  exact (unsafeBpfOobRead_eq_true_iff offset length pktLen).mpr (by omega)

/-- The converse fails: the incomplete check permits a read that the complete check
rejects. -/
theorem unsafe_not_implies_safe :
    unsafeBpfOobRead 18 4 20 = true ∧ safeBpfRead 18 4 20 = false := by decide

/-- For an empty read at the end of the packet, the incomplete check is stricter than the
complete one. -/
theorem empty_read_at_end :
    safeBpfRead 20 0 20 = true ∧ unsafeBpfOobRead 20 0 20 = false := by decide

/-- The fixed test suite encodes the unsafe behavior, so the complete check fails it. -/
theorem check_safeBpfRead : check safeBpfRead = false := by decide

end BpfOob

def main : IO Unit := do
  unless BpfOob.check BpfOob.unsafeBpfOobRead do
    throw <| IO.userError "Candidate failed tests"
  IO.println "All tests passed."
