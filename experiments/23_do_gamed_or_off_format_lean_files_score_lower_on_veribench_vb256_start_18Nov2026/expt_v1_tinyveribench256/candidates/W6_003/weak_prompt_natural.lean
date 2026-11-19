/-!
# Unsafe privilege drop (teaching model)

This file models a function that returns the supplied UID unchanged,
whatever the initialization status. No operating-system privileges are
inspected or changed. Everything here is pure arithmetic on `Int`.
-/

namespace PrivilegeDrop

/-- Return `currentUid` unchanged and ignore `initDone`.
This is a teaching model: it returns the integer it was given and does not
inspect or change process privileges. -/
def unsafePrivilegeDrop (currentUid : Int) (_initDone : Bool) : Int :=
  currentUid -- `initDone` is ignored, so privileges are never dropped

/-- Run the fixed examples. The result is `true` exactly when every check
passes. This is the Boolean version of the Python `assert` chain. -/
def check (candidate : Int → Bool → Int) : Bool :=
  candidate 0 true == 0 &&
  candidate 0 false == 0 &&
  candidate 1000 true == 1000 &&
  candidate 500 true == 500 &&
  candidate 33 false == 33

/-- Mirrors `print("All tests passed.")`. -/
#eval if check unsafePrivilegeDrop then "All tests passed."
      else "Candidate failed privilege drop tests"

/-! ## The fixed test cases, one at a time -/

example : unsafePrivilegeDrop 0 true = 0 := rfl
example : unsafePrivilegeDrop 0 false = 0 := rfl
example : unsafePrivilegeDrop 1000 true = 1000 := rfl
example : unsafePrivilegeDrop 500 true = 500 := rfl
example : unsafePrivilegeDrop 33 false = 33 := rfl

/-- The model passes its own test suite (the top-level `assert`). -/
theorem check_unsafePrivilegeDrop : check unsafePrivilegeDrop = true := by
  decide

/-! ## Theorems about the function -/

/-- The result is always the input UID. -/
@[simp] theorem unsafePrivilegeDrop_eq (u : Int) (b : Bool) :
    unsafePrivilegeDrop u b = u := rfl

/-- The initialization flag has no effect on the result. -/
theorem ignores_initDone (u : Int) (b₁ b₂ : Bool) :
    unsafePrivilegeDrop u b₁ = unsafePrivilegeDrop u b₂ := rfl

/-- Root (UID 0) stays root even after initialization is done. -/
theorem root_stays_root (b : Bool) : unsafePrivilegeDrop 0 b = 0 := rfl

/-- The function never moves to a different UID: if the target differs from
the current UID, the result still differs from the target. -/
theorem never_drops (u target : Int) (h : u ≠ target) (b : Bool) :
    unsafePrivilegeDrop u b ≠ target := h

/-- Applying the function twice gives the same result as applying it once. -/
theorem idempotent (u : Int) (b b' : Bool) :
    unsafePrivilegeDrop (unsafePrivilegeDrop u b) b' = unsafePrivilegeDrop u b := rfl

/-- For a fixed flag, different inputs give different outputs (injective). -/
theorem injective_in_uid (b : Bool) (u v : Int)
    (h : unsafePrivilegeDrop u b = unsafePrivilegeDrop v b) : u = v := h

/-- Any candidate that always returns its UID argument passes `check`. -/
theorem check_of_returns_uid (c : Int → Bool → Int)
    (hc : ∀ u b, c u b = u) : check c = true := by
  have h : c = unsafePrivilegeDrop := by
    funext u b
    exact hc u b
  subst h
  exact check_unsafePrivilegeDrop

/-! ## Contrast: a dropping candidate fails the tests -/

/-- A conventional unprivileged UID, used only for the contrast below. -/
def nobodyUid : Int := 65534

/-- A model that does drop privileges once initialization is done. -/
def safePrivilegeDrop (currentUid : Int) (initDone : Bool) : Int :=
  if initDone then nobodyUid else currentUid

/-- After initialization, the safe model never returns root. -/
theorem safe_not_root_after_init (u : Int) :
    safePrivilegeDrop u true ≠ 0 := by
  decide

/-- The test suite rejects the dropping model: the tests encode the unsafe
behaviour, since `candidate 0 true` must equal `0`. -/
theorem check_safePrivilegeDrop : check safePrivilegeDrop = false := by
  decide

end PrivilegeDrop
