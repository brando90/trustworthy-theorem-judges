import Mathlib
namespace Agent

/-!
# Safe IP fragment reassembly

A faithful model of the Python overlap checker. Offsets and lengths are integers;
nonpositive lengths generate no byte positions, exactly as Python's `range` does.
Payloads are lists of bytes and are deliberately never inspected. The received
set is represented by a list: only membership, not multiplicity or order, matters.
The specification characterizes acceptance by disjointness of every pair of
fragment ranges, and relates those finite ranges to integer half-open intervals.
-/

namespace SafeIPFragReassembly

structure Fragment where
  offset : Int
  length : Int
  data : List UInt8 := []
  deriving DecidableEq, Repr

/-- The integer positions visited by `range(offset, offset + length)`. -/
def byteRange (f : Fragment) : List Int :=
  (List.range f.length.toNat).map (fun n : Nat => f.offset + (n : Int))

/-- Visit bytes in fragment order and, within a fragment, in increasing order. -/
def positions (fs : List Fragment) : List Int := fs.flatMap byteRange

/-- Reject immediately if the next byte is already in the received set. -/
def scan (received : List Int) : List Int → Bool
  | [] => true
  | p :: ps => if p ∈ received then false else scan (p :: received) ps

def safe_reassemble (fs : List Fragment) : Bool := scan [] (positions fs)

-- The four Python checks, including their payloads.
def fragsOK : List Fragment :=
  [⟨0, 8, List.replicate 8 65⟩, ⟨8, 8, List.replicate 8 66⟩]
def fragsOverlap : List Fragment :=
  [⟨0, 16, List.replicate 16 65⟩, ⟨8, 16, List.replicate 16 66⟩]

example : safe_reassemble fragsOK = true := by native_decide
example : safe_reassemble fragsOverlap = false := by native_decide
example : safe_reassemble [] = true := by native_decide
example : safe_reassemble [⟨0, 8, List.replicate 8 67⟩] = true := by native_decide
-- Extra edge cases: negative offsets, empty ranges, and endpoint adjacency.
example : safe_reassemble [⟨-4, 4, []⟩, ⟨0, 3, []⟩] = true := by native_decide
example : safe_reassemble [⟨-4, 5, []⟩, ⟨0, 3, []⟩] = false := by native_decide
example : safe_reassemble [⟨0, -8, []⟩, ⟨0, 0, []⟩] = true := by native_decide
#eval (safe_reassemble fragsOK, safe_reassemble fragsOverlap,
  safe_reassemble [], safe_reassemble [⟨0, 8, List.replicate 8 67⟩])

/-- Executable counterpart of the Python `check()` entry point. -/
def check : IO Unit := do
  unless safe_reassemble fragsOK do
    throw (IO.userError "non-overlapping rejected")
  if safe_reassemble fragsOverlap then
    throw (IO.userError "overlapping should be rejected")
  unless safe_reassemble [] do
    throw (IO.userError "empty list rejected")
  unless safe_reassemble [⟨0, 8, List.replicate 8 67⟩] do
    throw (IO.userError "single fragment rejected")
  IO.println "All tests passed."

#eval check

/-- No restrictions: Python accepts arbitrary integer offsets and lengths. -/
def Pre (_fs : List Fragment) : Prop := True

/-- Mathematical half-open byte interval (empty when length is nonpositive). -/
def InRange (f : Fragment) (p : Int) : Prop :=
  f.offset ≤ p ∧ p < f.offset + f.length

/-- No two occurrences of fragments share a byte. Pairwise is by list position,
so identical fragments occurring twice are not accidentally identified. -/
def NoOverlap (fs : List Fragment) : Prop :=
  fs.Pairwise (fun f g => List.Disjoint (byteRange f) (byteRange g))


/-- A collision is witnessed by two distinct fragment occurrences and one byte. -/
def HasOverlap (fs : List Fragment) : Prop :=
  ∃ i j : Fin fs.length, i < j ∧
    ∃ p : Int, InRange (fs.get i) p ∧ InRange (fs.get j) p

/-- An independent, executable interval specification. -/
abbrev Separated (f g : Fragment) : Prop :=
  f.length ≤ 0 ∨ g.length ≤ 0 ∨
    f.offset + f.length ≤ g.offset ∨ g.offset + g.length ≤ f.offset

theorem mem_byteRange (f : Fragment) (p : Int) :
    p ∈ byteRange f ↔ InRange f p := by
  simp only [byteRange, List.mem_map, List.mem_range, InRange]
  constructor
  · rintro ⟨n, hn, rfl⟩
    omega
  · intro h
    refine ⟨(p - f.offset).toNat, ?_, ?_⟩ <;> omega

theorem byteRange_nodup (f : Fragment) : (byteRange f).Nodup := by
  unfold byteRange
  apply List.Nodup.map _ List.nodup_range
  intro a b h
  change f.offset + (a : Int) = f.offset + (b : Int) at h
  omega

/-- The loop invariant: the remaining bytes must be distinct and must avoid
all previously received bytes. The received list itself need not be distinct. -/
theorem scan_spec (received ps : List Int) :
    scan received ps = true ↔ ps.Nodup ∧ ∀ p ∈ ps, p ∉ received := by
  induction ps generalizing received with
  | nil => simp [scan]
  | cons p ps ih =>
    by_cases h : p ∈ received
    · simp [scan, h, List.nodup_cons]
    · simp [scan, h, ih, List.nodup_cons]
      grind

theorem safe_iff_nodup (fs : List Fragment) :
    safe_reassemble fs = true ↔ (positions fs).Nodup := by
  simpa [safe_reassemble] using scan_spec [] (positions fs)

def acceptance_prop (fs : List Fragment) : Prop :=
  safe_reassemble fs = true ↔ NoOverlap fs

theorem acceptance_thm (fs : List Fragment) : acceptance_prop fs := by
  unfold acceptance_prop
  rw [safe_iff_nodup, positions, List.nodup_flatMap]
  simp [NoOverlap, byteRange_nodup]

theorem disjoint_iff_separated (f g : Fragment) :
    List.Disjoint (byteRange f) (byteRange g) ↔ Separated f g := by
  simp only [List.Disjoint, mem_byteRange, InRange]
  constructor
  · intro h
    by_contra hn
    simp only [Separated, not_or, not_le] at hn
    have hf : f.offset ≤ max f.offset g.offset ∧
        max f.offset g.offset < f.offset + f.length := by
      omega
    have hg : g.offset ≤ max f.offset g.offset ∧
        max f.offset g.offset < g.offset + g.length := by
      omega
    exact h hf hg
  · intro h p hf hg
    rcases h with h | h | h | h <;> omega

theorem interval_spec_thm (fs : List Fragment) :
    safe_reassemble fs = true ↔ fs.Pairwise Separated := by
  rw [show safe_reassemble fs = true ↔ NoOverlap fs from acceptance_thm fs]
  simp only [NoOverlap, List.pairwise_iff_get, disjoint_iff_separated]

theorem overlap_iff_not_noOverlap (fs : List Fragment) :
    HasOverlap fs ↔ ¬ NoOverlap fs := by
  classical
  simp only [HasOverlap, NoOverlap, List.pairwise_iff_get, List.Disjoint,
    mem_byteRange]
  push_neg
  simp

def rejection_prop (fs : List Fragment) : Prop :=
  safe_reassemble fs = false ↔ HasOverlap fs

theorem rejection_thm (fs : List Fragment) : rejection_prop fs := by
  unfold rejection_prop
  have h : safe_reassemble fs = true ↔ NoOverlap fs := acceptance_thm fs
  rw [overlap_iff_not_noOverlap, ← h]
  cases safe_reassemble fs <;> simp

theorem empty_thm : safe_reassemble [] = true := rfl

def singleton_prop (f : Fragment) : Prop := safe_reassemble [f] = true

theorem singleton_thm (f : Fragment) : singleton_prop f := by
  apply (acceptance_thm [f]).mpr
  simp [NoOverlap]

/-- Payload lengths need not equal the declared lengths, as in the Python code. -/
def shape (f : Fragment) : Int × Int := (f.offset, f.length)

def payload_prop (fs gs : List Fragment) : Prop :=
  fs.map shape = gs.map shape → safe_reassemble fs = safe_reassemble gs

theorem payload_thm (fs gs : List Fragment) : payload_prop fs gs := by
  intro h
  have hp := congrArg (fun rs : List (Int × Int) =>
    rs.flatMap (fun r => (List.range r.2.toNat).map (fun n : Nat => r.1 + (n : Int)))) h
  have he : positions fs = positions gs := by
    simpa [positions, byteRange, shape, List.flatMap_map] using hp
  simp only [safe_reassemble, he]

def permutation_prop (fs gs : List Fragment) : Prop :=
  fs.Perm gs → safe_reassemble fs = safe_reassemble gs

theorem permutation_thm (fs gs : List Fragment) : permutation_prop fs gs := by
  intro h
  have hn : (positions fs).Nodup ↔ (positions gs).Nodup :=
    (h.flatMap (fun f _ => List.Perm.refl (byteRange f))).nodup_iff
  have he : safe_reassemble fs = true ↔ safe_reassemble gs = true :=
    (safe_iff_nodup fs).trans (hn.trans (safe_iff_nodup gs).symm)
  simpa using he

def extension_prop (fs gs : List Fragment) : Prop :=
  safe_reassemble fs = false → safe_reassemble (fs ++ gs) = false

theorem extension_thm (fs gs : List Fragment) : extension_prop fs gs := by
  intro h
  cases he : safe_reassemble (fs ++ gs) with
  | false => rfl
  | true =>
    have hn := (acceptance_thm (fs ++ gs)).mp he
    have hf : NoOverlap fs := (List.pairwise_append.mp hn).1
    have ht := (acceptance_thm fs).mpr hf
    simp [h] at ht

/-- Exact acceptance and exact rejection: neither false negatives nor false
positives, including empty ranges and duplicate fragment occurrences. -/
def Post_prop (fs : List Fragment) : Prop :=
  acceptance_prop fs ∧ rejection_prop fs


/-! ## Bounded property-based tests

These are exhaustive over all lists of length at most three from 25 fragment
shapes (offsets -2..2, lengths -1..3): 16,276 lists. The test oracle uses only
interval endpoints, not the implementation's byte-by-byte scanning algorithm.
Theorems above retain the full, unbounded integer/list domain.
-/

def specAccept (fs : List Fragment) : Bool := decide (fs.Pairwise Separated)

def smallFragments : List Fragment :=
  (List.range 5).flatMap fun o => (List.range 5).map fun l =>
    ⟨(o : Int) - 2, (l : Int) - 1, []⟩

def listsOfLength {α : Type} (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap fun a => (listsOfLength alphabet n).map (a :: ·)

def sampleLists : List (List Fragment) :=
  (List.range 4).flatMap (listsOfLength smallFragments)

-- PBT for acceptance_prop: exact agreement with pairwise interval separation.
example : sampleLists.all (fun fs => safe_reassemble fs == specAccept fs) = true := by
  native_decide

-- PBT for rejection_prop: a collision exists exactly when some pair of
-- nonempty half-open intervals is not separated (see overlap_iff_not_noOverlap).
example : sampleLists.all (fun fs =>
    (safe_reassemble fs == false) == (!specAccept fs)) = true := by
  native_decide

-- PBT for singleton_prop, including negative and zero lengths.
example : smallFragments.all (fun f => safe_reassemble [f]) = true := by
  native_decide

-- PBT for payload_prop: deliberately vary payload lengths and contents
-- separately at each index, while generating its shape-equality premise.
example : sampleLists.all (fun fs => (List.range 4).all (fun salt =>
    let gs := fs.mapIdx (fun i f =>
      { f with data := List.replicate ((i + salt) % 5) (UInt8.ofNat (i + salt)) })
    decide (fs.map shape = gs.map shape) &&
      (safe_reassemble fs == safe_reassemble gs))) = true := by
  native_decide

-- PBT for permutation_prop: test every permutation, so the premise is never
-- vacuous. Duplicate occurrences and empty ranges are included.
example : sampleLists.all (fun fs => fs.permutations.all (fun gs =>
    safe_reassemble fs == safe_reassemble gs)) = true := by
  native_decide

-- PBT for extension_prop: append every small singleton or the empty list.
example : sampleLists.all (fun fs => ([[]] ++ smallFragments.map (fun f => [f])).all
    (fun gs => safe_reassemble fs || !safe_reassemble (fs ++ gs))) = true := by
  native_decide

-- Additional PBT connecting the executable ranges to Python's integer bounds.
example : smallFragments.all (fun f => (List.range 13).all (fun n =>
    let p := (n : Int) - 5
    decide (p ∈ byteRange f) == decide (f.offset ≤ p ∧ p < f.offset + f.length)))
    = true := by native_decide

-- PBT for Post_prop: the conjunction of exact acceptance and exact rejection.
def postCheck (fs : List Fragment) : Bool :=
  ((safe_reassemble fs == true) == specAccept fs) &&
  ((safe_reassemble fs == false) == !specAccept fs)

example : sampleLists.all postCheck = true := by native_decide
#eval (sampleLists.length, sampleLists.all postCheck)

/-- Kernel-checked correctness; the tests are not used by this proof. -/
theorem correctness_thm (fs : List Fragment) : Pre fs → Post_prop fs := by
  intro _
  exact ⟨acceptance_thm fs, rejection_thm fs⟩


/-! ## Imperative implementation

`positions` linearizes the two Python loops in their original visiting order.
The loop below maintains the mutable received set and returns immediately at
its first collision. As in the functional model, a membership-only list is a
representation of the Python set; no byte buffer or payload is needed.
-/

def scanImperative (received : List Int) (ps : List Int) : Bool := Id.run do
  let mut seen := received
  for p in ps do
    if p ∈ seen then
      return false
    seen := p :: seen
  return true

def safe_reassemble_imperative (fs : List Fragment) : Bool := Id.run do
  let mut received : List Int := []
  for p in positions fs do
    if p ∈ received then
      return false
    received := p :: received
  return true

-- The original unit tests, now for the mutable implementation.
example : safe_reassemble_imperative fragsOK = true := by native_decide
example : safe_reassemble_imperative fragsOverlap = false := by native_decide
example : safe_reassemble_imperative [] = true := by native_decide
example : safe_reassemble_imperative [⟨0, 8, List.replicate 8 67⟩] = true := by
  native_decide
example : safe_reassemble_imperative [⟨-4, 5, []⟩, ⟨0, 3, []⟩] = false := by
  native_decide
example : safe_reassemble_imperative [⟨-4, -2, []⟩, ⟨0, 0, []⟩] = true := by
  native_decide
#eval (safe_reassemble_imperative fragsOK, safe_reassemble_imperative fragsOverlap,
  safe_reassemble_imperative [],
  safe_reassemble_imperative [⟨0, 8, List.replicate 8 67⟩])

-- Bounded PBT for equivalence, independent of the proof below.
example : sampleLists.all (fun fs =>
    safe_reassemble fs == safe_reassemble_imperative fs) = true := by
  native_decide

/-- The mutable loop agrees with the functional scanner for every initial
received set, including lists with duplicate entries. -/
theorem scanImperative_eq_scan (received ps : List Int) :
    scanImperative received ps = scan received ps := by
  induction ps generalizing received with
  | nil => simp [scanImperative, scan]
  | cons p ps ih =>
    simp only [scanImperative, List.forIn_cons, scan]
    split
    · simp_all
    · simpa [scanImperative] using ih (p :: received)

/-- Unconditional equivalence, with arbitrary integer offsets and lengths and
arbitrary byte payloads. No test result is used in this kernel-checked proof. -/
theorem equivalence_thm (fs : List Fragment) :
    safe_reassemble fs = safe_reassemble_imperative fs := by
  change scan [] (positions fs) = scanImperative [] (positions fs)
  exact (scanImperative_eq_scan [] (positions fs)).symm

end SafeIPFragReassembly
end Agent
