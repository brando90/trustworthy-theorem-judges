import Mathlib
namespace Agent

/-!
# Unsafe last-level-cache partition

Translation of the Python `unsafeLLCAccess` function and its checks.
The only access criterion is `cache_set < total_sets`; the process ID is
ignored. Consequently, distinct processes can access the same cache set.
This models the missing isolation underlying the described timing channel,
not cache eviction or timing measurements themselves.

All arguments are `Int`, preserving Python's integer domain, including
negative arguments. In particular, the code does not check `0 ≤ cache_set`
and does not require a positive number of sets. The precondition is therefore
unrestricted. Bounded property tests cover both negative and nonnegative
inputs; all named proofs apply to arbitrary integers and are kernel-checked.
-/

namespace UnsafeLLCPartition

/-! ## Functional implementation -/

/-- The requesting process has no influence on the access decision. -/
def unsafeLLCAccess (_process_id cache_set total_sets : Int) : Bool :=
  decide (cache_set < total_sets)

/-! ## Unit tests and the Python check routine -/

example : unsafeLLCAccess 0 5 16 = true := by native_decide
example : unsafeLLCAccess 1 5 16 = true := by native_decide
example : unsafeLLCAccess 0 15 16 = true := by native_decide
example : unsafeLLCAccess 0 16 16 = false := by native_decide

-- Extra checks expose the precise integer semantics, with no lower-bound test.
example : unsafeLLCAccess (-7) (-1) 16 = true := by native_decide
example : unsafeLLCAccess 3 (-3) (-2) = true := by native_decide
example : unsafeLLCAccess 3 (-2) (-2) = false := by native_decide
example : unsafeLLCAccess 0 0 0 = false := by native_decide
example : unsafeLLCAccess 0 17 16 = false := by native_decide

/-- Boolean version of the four assertions in Python's `check`. -/
def check : Bool :=
  unsafeLLCAccess 0 5 16 &&
  unsafeLLCAccess 1 5 16 &&
  unsafeLLCAccess 0 15 16 &&
  !(unsafeLLCAccess 0 16 16)

example : check = true := by native_decide
#eval check
#eval if check then "All tests passed." else "A test failed."

/-! ## Precondition -/

/-- Python imposes no restrictions beyond the integer input types. -/
def Pre (_process_id _cache_set _total_sets : Int) : Prop := True

/-! ## Properties and kernel-checked proofs -/

/-- Exact acceptance criterion, including negative integer arguments. -/
def access_iff_prop (process_id cache_set total_sets : Int) : Prop :=
  unsafeLLCAccess process_id cache_set total_sets = true ↔ cache_set < total_sets

theorem access_iff_thm (process_id cache_set total_sets : Int) :
    access_iff_prop process_id cache_set total_sets := by
  simp [access_iff_prop, unsafeLLCAccess]

/-- At or above the upper bound, access is denied, and only there. -/
def denial_iff_prop (process_id cache_set total_sets : Int) : Prop :=
  unsafeLLCAccess process_id cache_set total_sets = false ↔ total_sets ≤ cache_set

theorem denial_iff_thm (process_id cache_set total_sets : Int) :
    denial_iff_prop process_id cache_set total_sets := by
  simp [denial_iff_prop, unsafeLLCAccess, not_lt]

/-- All process IDs receive exactly the same decision. -/
def process_independent_prop (process_id other_process cache_set total_sets : Int) : Prop :=
  unsafeLLCAccess process_id cache_set total_sets =
    unsafeLLCAccess other_process cache_set total_sets

theorem process_independent_thm
    (process_id other_process cache_set total_sets : Int) :
    process_independent_prop process_id other_process cache_set total_sets := by
  rfl

/-- Every set below the upper bound is accessible to both processes.
No equality of process IDs is assumed: this also covers distinct processes. -/
def shared_access_prop (process_id other_process cache_set total_sets : Int) : Prop :=
  cache_set < total_sets →
    unsafeLLCAccess process_id cache_set total_sets = true ∧
    unsafeLLCAccess other_process cache_set total_sets = true

theorem shared_access_thm (process_id other_process cache_set total_sets : Int) :
    shared_access_prop process_id other_process cache_set total_sets := by
  unfold shared_access_prop
  intro h
  simp [unsafeLLCAccess, h]

/-- The upper boundary itself is excluded for every process. -/
def boundary_prop (process_id total_sets : Int) : Prop :=
  unsafeLLCAccess process_id total_sets total_sets = false

theorem boundary_thm (process_id total_sets : Int) :
    boundary_prop process_id total_sets := by
  simp [boundary_prop, unsafeLLCAccess]

/-! ## Postcondition -/

/-- Exact decision semantics together with the absence of process isolation. -/
def Post_prop (process_id cache_set total_sets : Int) : Prop :=
  access_iff_prop process_id cache_set total_sets ∧
  denial_iff_prop process_id cache_set total_sets ∧
  (∀ other_process : Int,
    process_independent_prop process_id other_process cache_set total_sets) ∧
  (∀ other_process : Int,
    shared_access_prop process_id other_process cache_set total_sets) ∧
  boundary_prop process_id total_sets

/-! ## Property-based tests

Each executable property and the full postcondition has its own bounded,
exhaustive Boolean check. Every input position ranges over all integers from
-4 through 20. These finite checks are evidence, not premises of any theorem.
-/

def pbtInputs : List Int := (List.range 25).map (fun n => (n : Int) - 4)

-- PBT for access_iff_prop.
def accessPBT : Bool :=
  pbtInputs.all fun p => pbtInputs.all fun c => pbtInputs.all fun t =>
    (unsafeLLCAccess p c t == true) == decide (c < t)

example : accessPBT = true := by native_decide

-- PBT for denial_iff_prop.
def denialPBT : Bool :=
  pbtInputs.all fun p => pbtInputs.all fun c => pbtInputs.all fun t =>
    (unsafeLLCAccess p c t == false) == decide (t ≤ c)

example : denialPBT = true := by native_decide

-- PBT for process_independent_prop, including distinct process pairs.
def independencePBT : Bool :=
  pbtInputs.all fun p => pbtInputs.all fun q =>
    pbtInputs.all fun c => pbtInputs.all fun t =>
      unsafeLLCAccess p c t == unsafeLLCAccess q c t

example : independencePBT = true := by native_decide

-- PBT for shared_access_prop; implication is checked as a Boolean conditional.
def sharedAccessPBT : Bool :=
  pbtInputs.all fun p => pbtInputs.all fun q =>
    pbtInputs.all fun c => pbtInputs.all fun t =>
      if c < t then unsafeLLCAccess p c t && unsafeLLCAccess q c t else true

example : sharedAccessPBT = true := by native_decide

-- PBT for boundary_prop.
def boundaryPBT : Bool :=
  pbtInputs.all fun p => pbtInputs.all fun t =>
    unsafeLLCAccess p t t == false

example : boundaryPBT = true := by native_decide

-- PBT for Post_prop: check every conjunct, bounding its other-process quantifiers.
def postPBT : Bool :=
  pbtInputs.all fun p => pbtInputs.all fun c => pbtInputs.all fun t =>
    ((unsafeLLCAccess p c t == true) == decide (c < t)) &&
    ((unsafeLLCAccess p c t == false) == decide (t ≤ c)) &&
    (pbtInputs.all fun q => unsafeLLCAccess p c t == unsafeLLCAccess q c t) &&
    (pbtInputs.all fun q =>
      if c < t then unsafeLLCAccess p c t && unsafeLLCAccess q c t else true) &&
    (unsafeLLCAccess p t t == false)

example : postPBT = true := by native_decide

#eval [("access", accessPBT), ("denial", denialPBT),
  ("process independence", independencePBT), ("shared access", sharedAccessPBT),
  ("boundary", boundaryPBT), ("postcondition", postPBT)]

/-! ## Correctness -/

theorem correctness_thm (process_id cache_set total_sets : Int) :
    Pre process_id cache_set total_sets → Post_prop process_id cache_set total_sets := by
  intro _h
  exact ⟨access_iff_thm process_id cache_set total_sets,
    denial_iff_thm process_id cache_set total_sets,
    (fun other => process_independent_thm process_id other cache_set total_sets),
    (fun other => shared_access_thm process_id other cache_set total_sets),
    boundary_thm process_id total_sets⟩

/-! ## Imperative implementation -/

/-- Mutable-state implementation of the same strict comparison. -/
def unsafeLLCAccessImperative (_process_id cache_set total_sets : Int) : Bool := Id.run do
  let mut allowed := false
  if cache_set < total_sets then
    allowed := true
  return allowed

/-! ## Imperative tests -/

example : unsafeLLCAccessImperative 0 5 16 = true := by native_decide
example : unsafeLLCAccessImperative 1 5 16 = true := by native_decide
example : unsafeLLCAccessImperative 0 15 16 = true := by native_decide
example : unsafeLLCAccessImperative 0 16 16 = false := by native_decide
example : unsafeLLCAccessImperative (-7) (-1) 16 = true := by native_decide
example : unsafeLLCAccessImperative 3 (-3) (-2) = true := by native_decide
example : unsafeLLCAccessImperative 0 0 0 = false := by native_decide

#eval [unsafeLLCAccessImperative 0 5 16, unsafeLLCAccessImperative 1 5 16,
  unsafeLLCAccessImperative 0 15 16, unsafeLLCAccessImperative 0 16 16]

-- Bounded functional/imperative comparison over the same signed input domain.
example : (pbtInputs.all fun p => pbtInputs.all fun c => pbtInputs.all fun t =>
    unsafeLLCAccess p c t == unsafeLLCAccessImperative p c t) = true := by
  native_decide

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equivalence_thm (process_id cache_set total_sets : Int) :
    unsafeLLCAccess process_id cache_set total_sets =
      unsafeLLCAccessImperative process_id cache_set total_sets := by
  by_cases h : cache_set < total_sets <;>
    simp [unsafeLLCAccess, unsafeLLCAccessImperative, h]

end UnsafeLLCPartition
end Agent
