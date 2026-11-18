import Mathlib
namespace Agent

/-!
# Safe signed key rotation

Lean 4 formalization of the Python program `103_unsafeUnsignedKeyRotation_safe.py`
(MIT 6.858 L17, "safe" variant).

A key rotation request carries an old key, a proposed new key, and a flag saying
whether the request was signed by the *old* key.  The safe policy accepts the
rotation (returning the new key) exactly when the signature by the old key is
present, and rejects it (returning `none`) otherwise.  Crucially, the decision
does not depend on the old key value at all — only on the signature flag.

Contents:
* `safeRotate`      — functional implementation (Python `safe_rotate`),
* `rotationAccepted` — Python `rotation_accepted`,
* unit tests mirroring Python's `check`,
* pre/post-conditions and the correctness theorem,
* `safeRotateImp`   — imperative implementation via `Id.run do` with mutable state,
* the equivalence theorem between the two implementations.
-/

namespace «103_unsafeUnsignedKeyRotation_safe»

/-! ## Functional implementation -/

/-- `safe_rotate(_old_key, new_key, signed_by_old)`:
returns the new key when the request is signed by the old key, `none` otherwise. -/
def safeRotate (_oldKey newKey : Int) (signedByOld : Bool) : Option Int :=
  if signedByOld then some newKey else none

/-- `rotation_accepted(old_key, new_key, signed)`:
the rotation is accepted iff `safe_rotate` returned a key. -/
def rotationAccepted (oldKey newKey : Int) (signed : Bool) : Bool :=
  (safeRotate oldKey newKey signed).isSome

/-! ## Unit tests (mirroring Python's `check`) -/

example : safeRotate 100 200 true = some 200 := by native_decide
example : safeRotate 100 200 false = none := by native_decide
example : safeRotate 0 0 true = some 0 := by native_decide
example : safeRotate 100 9999 false = none := by native_decide

example : rotationAccepted 1 2 true = true := by native_decide
example : rotationAccepted 1 999 false = false := by native_decide

example : ([0, 1, 100] : List Int).all (fun o => rotationAccepted o 999 true) = true := by
  native_decide
example : ([0, 1, 100] : List Int).all (fun o => !rotationAccepted o 999 false) = true := by
  native_decide

#eval safeRotate 100 200 true
#eval safeRotate 100 200 false
#eval safeRotate 0 0 true
#eval rotationAccepted 1 2 true
#eval rotationAccepted 1 999 false

/-! ## Pre-condition -/

/-- The Python function is total: it accepts arbitrary integer keys and an
arbitrary boolean flag, so the pre-condition is trivially true. -/
def Pre (_oldKey _newKey : Int) (_signedByOld : Bool) : Prop := True

/-! ## Properties -/

/-- A rotation signed by the old key is accepted and installs exactly the new key. -/
def signed_accepts_prop : Prop :=
  ∀ oldKey newKey : Int, safeRotate oldKey newKey true = some newKey

theorem signed_accepts_thm : signed_accepts_prop := by
  intro oldKey newKey
  simp [safeRotate]

/-- An unsigned rotation is always rejected: this is the safety property that the
"unsafe" variant of the program violates. -/
def unsigned_rejects_prop : Prop :=
  ∀ oldKey newKey : Int, safeRotate oldKey newKey false = none

theorem unsigned_rejects_thm : unsigned_rejects_prop := by
  intro oldKey newKey
  simp [safeRotate]

/-- The outcome never depends on the old key value. -/
def oldKey_irrelevant_prop : Prop :=
  ∀ oldKey oldKey' newKey : Int, ∀ signed : Bool,
    safeRotate oldKey newKey signed = safeRotate oldKey' newKey signed

theorem oldKey_irrelevant_thm : oldKey_irrelevant_prop := by
  intro oldKey oldKey' newKey signed
  cases signed <;> simp [safeRotate]

/-- Whenever a key is returned, it is exactly the requested new key and the
request was signed. -/
def result_sound_prop : Prop :=
  ∀ oldKey newKey k : Int, ∀ signed : Bool,
    safeRotate oldKey newKey signed = some k → k = newKey ∧ signed = true

theorem result_sound_thm : result_sound_prop := by
  intro oldKey newKey k signed h
  cases signed <;> simp [safeRotate] at h ⊢
  exact h.symm

/-- `rotation_accepted` is precisely the signature flag. -/
def accepted_iff_signed_prop : Prop :=
  ∀ oldKey newKey : Int, ∀ signed : Bool,
    rotationAccepted oldKey newKey signed = signed

theorem accepted_iff_signed_thm : accepted_iff_signed_prop := by
  intro oldKey newKey signed
  cases signed <;> simp [rotationAccepted, safeRotate]

/-- Full specification of the return value, by case on the flag. -/
def spec_prop : Prop :=
  ∀ oldKey newKey : Int, ∀ signed : Bool,
    safeRotate oldKey newKey signed = if signed then some newKey else none

theorem spec_thm : spec_prop := by
  intro oldKey newKey signed
  cases signed <;> simp [safeRotate]

/-- All assertions of Python's `check` hold. -/
def check_prop : Prop :=
  safeRotate 100 200 true = some 200 ∧
  safeRotate 100 200 false = none ∧
  safeRotate 0 0 true = some 0 ∧
  safeRotate 100 9999 false = none ∧
  rotationAccepted 1 2 true = true ∧
  rotationAccepted 1 999 false = false ∧
  (∀ o ∈ ([0, 1, 100] : List Int),
    rotationAccepted o 999 true = true ∧ rotationAccepted o 999 false = false)

theorem check_thm : check_prop := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro o _
  exact ⟨by simp [rotationAccepted, safeRotate], by simp [rotationAccepted, safeRotate]⟩

/-! ## Post-condition and correctness -/

/-- Post-condition: the conjunction of all the properties above. -/
def Post_prop : Prop :=
  signed_accepts_prop ∧
  unsigned_rejects_prop ∧
  oldKey_irrelevant_prop ∧
  result_sound_prop ∧
  accepted_iff_signed_prop ∧
  spec_prop ∧
  check_prop

/-- Correctness: the pre-condition implies the post-condition. -/
theorem correctness (oldKey newKey : Int) (signedByOld : Bool)
    (_h : Pre oldKey newKey signedByOld) : Post_prop :=
  ⟨signed_accepts_thm, unsigned_rejects_thm, oldKey_irrelevant_thm, result_sound_thm,
    accepted_iff_signed_thm, spec_thm, check_thm⟩

/-! ## Imperative implementation -/

/-- Imperative version of `safe_rotate` using a mutable result register:
start with "rejected" and only overwrite it when the old-key signature is present. -/
def safeRotateImp (_oldKey newKey : Int) (signedByOld : Bool) : Option Int := Id.run do
  let mut result : Option Int := none
  if signedByOld then
    result := some newKey
  return result

/-- Imperative version of `rotation_accepted`. -/
def rotationAcceptedImp (oldKey newKey : Int) (signed : Bool) : Bool := Id.run do
  let mut accepted := false
  match safeRotateImp oldKey newKey signed with
  | some _ => accepted := true
  | none => accepted := false
  return accepted

/-! ## Imperative tests -/

example : safeRotateImp 100 200 true = some 200 := by native_decide
example : safeRotateImp 100 200 false = none := by native_decide
example : safeRotateImp 0 0 true = some 0 := by native_decide
example : safeRotateImp 100 9999 false = none := by native_decide
example : rotationAcceptedImp 1 2 true = true := by native_decide
example : rotationAcceptedImp 1 999 false = false := by native_decide

#eval safeRotateImp 100 200 true
#eval safeRotateImp 100 200 false
#eval rotationAcceptedImp 1 999 false

/-! ## Equivalence -/

/-- The functional and imperative implementations of `safe_rotate` agree. -/
theorem safeRotate_eq_imp (oldKey newKey : Int) (signedByOld : Bool) :
    safeRotate oldKey newKey signedByOld = safeRotateImp oldKey newKey signedByOld := by
  cases signedByOld <;> rfl

/-- The functional and imperative implementations of `rotation_accepted` agree. -/
theorem rotationAccepted_eq_imp (oldKey newKey : Int) (signed : Bool) :
    rotationAccepted oldKey newKey signed = rotationAcceptedImp oldKey newKey signed := by
  cases signed <;> rfl

/-- Point-free form of the equivalence. -/
theorem safeRotate_eq_imp' : safeRotate = safeRotateImp := by
  funext oldKey newKey signedByOld
  exact safeRotate_eq_imp oldKey newKey signedByOld

end «103_unsafeUnsignedKeyRotation_safe»
end Agent
