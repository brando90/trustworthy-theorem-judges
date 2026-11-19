/-!
# Safe signature permission grant

This file translates a Python function to Lean 4. It grants a permission only
when the app and the owner have the same signing certificate.

The Python `int` type becomes Lean's `Int`, and the Python `bool` type becomes
`Bool`.
-/

namespace SafeSigPerm

/-- Returns `true` only when `appCert = ownerCert`. -/
def safeSigPermGrant (appCert ownerCert : Int) : Bool :=
  appCert == ownerCert

/-! ## Fixed examples (same as the Python `check` function) -/

/-- Runs the same fixed examples as the Python `check` function. It is `true`
only when every observation matches. -/
def check : Bool :=
  safeSigPermGrant 1 1 == true &&
  safeSigPermGrant 1 2 == false &&
  safeSigPermGrant 0 999 == false &&
  safeSigPermGrant 42 42 == true &&
  safeSigPermGrant 0 0 == true

theorem check_passes : check = true := by decide

example : safeSigPermGrant 1 1 = true := by decide
example : safeSigPermGrant 1 2 = false := by decide
example : safeSigPermGrant 0 999 = false := by decide
example : safeSigPermGrant 42 42 = true := by decide
example : safeSigPermGrant 0 0 = true := by decide

/-! ## Specification theorems -/

/-- Main specification: the function grants the permission exactly when the
certificates are equal. -/
theorem safeSigPermGrant_iff (a b : Int) :
    safeSigPermGrant a b = true ↔ a = b := by
  simp [safeSigPermGrant]

/-- The function denies the permission exactly when the certificates differ. -/
theorem safeSigPermGrant_eq_false_iff (a b : Int) :
    safeSigPermGrant a b = false ↔ a ≠ b := by
  simp [safeSigPermGrant]

/-- Soundness: a granted permission means the certificates are equal. -/
theorem safeSigPermGrant_sound {a b : Int}
    (h : safeSigPermGrant a b = true) : a = b :=
  (safeSigPermGrant_iff a b).mp h

/-- Safety: certificates that differ never get a grant. -/
theorem safeSigPermGrant_denies_mismatch {a b : Int}
    (h : a ≠ b) : safeSigPermGrant a b = false :=
  (safeSigPermGrant_eq_false_iff a b).mpr h

/-- Completeness: an app signed with the owner's certificate always gets a
grant. -/
theorem safeSigPermGrant_refl (a : Int) : safeSigPermGrant a a = true :=
  (safeSigPermGrant_iff a a).mpr rfl

/-- The result is the same if the app and owner swap places. -/
theorem safeSigPermGrant_comm (a b : Int) :
    safeSigPermGrant a b = safeSigPermGrant b a := by
  by_cases h : a = b
  · subst h
    rfl
  · rw [safeSigPermGrant_denies_mismatch h,
        safeSigPermGrant_denies_mismatch (Ne.symm h)]

/-- Grants chain: if `a` matches `b` and `b` matches `c`, then `a` matches
`c`. -/
theorem safeSigPermGrant_trans {a b c : Int}
    (h₁ : safeSigPermGrant a b = true) (h₂ : safeSigPermGrant b c = true) :
    safeSigPermGrant a c = true :=
  (safeSigPermGrant_iff a c).mpr
    ((safeSigPermGrant_sound h₁).trans (safeSigPermGrant_sound h₂))

/-- Only one app certificate can get a grant for a given owner certificate. -/
theorem granted_app_unique {a₁ a₂ owner : Int}
    (h₁ : safeSigPermGrant a₁ owner = true)
    (h₂ : safeSigPermGrant a₂ owner = true) :
    a₁ = a₂ :=
  (safeSigPermGrant_sound h₁).trans (safeSigPermGrant_sound h₂).symm

/-- The function returns the same result as the decision procedure for
equality. -/
theorem safeSigPermGrant_eq_decide (a b : Int) :
    safeSigPermGrant a b = decide (a = b) := by
  by_cases h : a = b
  · rw [(safeSigPermGrant_iff a b).mpr h, decide_eq_true h]
  · rw [safeSigPermGrant_denies_mismatch h, decide_eq_false h]

/-- Adding the same number to both certificates does not change the
result. -/
theorem safeSigPermGrant_add_right (a b k : Int) :
    safeSigPermGrant (a + k) (b + k) = safeSigPermGrant a b := by
  by_cases h : a = b
  · subst h
    rw [safeSigPermGrant_refl, safeSigPermGrant_refl]
  · have h' : a + k ≠ b + k := by omega
    rw [safeSigPermGrant_denies_mismatch h', safeSigPermGrant_denies_mismatch h]

end SafeSigPerm
