/-!
# Safe cookie domain check

This is a Lean 4 translation of a Python program. A cookie is accepted only
when its domain equals the current origin. Python `int` becomes Lean `Int`,
and Python `bool` becomes Lean `Bool`.
-/

namespace SafeCookie

/-- Returns `true` only when `cookieDomain = currentDomain`. -/
def safeCookieDomain (cookieDomain currentDomain : Int) : Bool :=
  cookieDomain == currentDomain

/-! ## Fixed examples (mirrors Python `check`) -/

example : safeCookieDomain 1 1 = true := by decide
example : safeCookieDomain 1 2 = false := by decide
example : safeCookieDomain 0 999 = false := by decide
example : safeCookieDomain 42 42 = true := by decide
example : safeCookieDomain 0 0 = true := by decide

/-- Executable version of Python's `check`: `true` when every assertion holds. -/
def check : Bool :=
  (safeCookieDomain 1 1 == true) &&
  (safeCookieDomain 1 2 == false) &&
  (safeCookieDomain 0 999 == false) &&
  (safeCookieDomain 42 42 == true) &&
  (safeCookieDomain 0 0 == true)

/-- All of the fixed examples pass. -/
theorem check_passes : check = true := by decide

/-! ## Theorems -/

/-- Specification: a cookie is accepted exactly when the two domains are equal. -/
theorem safeCookieDomain_iff (a b : Int) :
    safeCookieDomain a b = true ↔ a = b := by
  simp [safeCookieDomain]

/-- Soundness: an accepted cookie always has the current origin's domain. -/
theorem accepted_implies_match {a b : Int} (h : safeCookieDomain a b = true) :
    a = b :=
  (safeCookieDomain_iff a b).mp h

/-- Completeness: a cookie whose domain matches the current origin is accepted. -/
theorem match_implies_accepted {a b : Int} (h : a = b) :
    safeCookieDomain a b = true :=
  (safeCookieDomain_iff a b).mpr h

/-- A cookie is rejected exactly when the two domains differ. -/
theorem safeCookieDomain_eq_false_iff (a b : Int) :
    safeCookieDomain a b = false ↔ a ≠ b := by
  constructor
  · intro h heq
    have hT : safeCookieDomain a b = true := match_implies_accepted heq
    rw [h] at hT
    contradiction
  · intro hne
    cases h : safeCookieDomain a b with
    | false => rfl
    | true => exact absurd (accepted_implies_match h) hne

/-- Safety: a cookie from a different domain is always rejected. -/
theorem mismatch_rejected {a b : Int} (h : a ≠ b) :
    safeCookieDomain a b = false :=
  (safeCookieDomain_eq_false_iff a b).mpr h

/-- Reflexivity: a domain always accepts its own cookies. -/
theorem safeCookieDomain_refl (a : Int) : safeCookieDomain a a = true :=
  match_implies_accepted rfl

/-- Symmetry: swapping the cookie domain and the current domain gives the same result. -/
theorem safeCookieDomain_comm (a b : Int) :
    safeCookieDomain a b = safeCookieDomain b a := by
  by_cases h : a = b
  · subst h
    rfl
  · rw [mismatch_rejected h, mismatch_rejected (fun h' => h h'.symm)]

/-- Transitivity: acceptance chains across domains. -/
theorem safeCookieDomain_trans {a b c : Int}
    (h₁ : safeCookieDomain a b = true) (h₂ : safeCookieDomain b c = true) :
    safeCookieDomain a c = true :=
  match_implies_accepted ((accepted_implies_match h₁).trans (accepted_implies_match h₂))

/-- Uniqueness: for a fixed origin, at most one cookie domain is accepted. -/
theorem accepted_domain_unique {c₁ c₂ cur : Int}
    (h₁ : safeCookieDomain c₁ cur = true) (h₂ : safeCookieDomain c₂ cur = true) :
    c₁ = c₂ :=
  (accepted_implies_match h₁).trans (accepted_implies_match h₂).symm

/-- The check is the decision procedure for domain equality. -/
theorem safeCookieDomain_eq_decide (a b : Int) :
    safeCookieDomain a b = decide (a = b) := by
  by_cases h : a = b
  · rw [decide_eq_true h, match_implies_accepted h]
  · rw [decide_eq_false h, mismatch_rejected h]

/-- Every origin rejects some cookie domain, so the check is never "accept all". -/
theorem exists_rejected (cur : Int) : ∃ c, safeCookieDomain c cur = false :=
  ⟨cur + 1, mismatch_rejected (by omega)⟩

end SafeCookie

/-- Entry point, mirroring Python's `if __name__ == "__main__": check()`. -/
def main : IO Unit := do
  unless SafeCookie.check do
    throw <| IO.userError "AssertionError: safeCookieDomain check failed"

-- TLDR-end: [lean: safeCookieDomain] This file translates the check to Lean 4 and proves that a cookie is accepted exactly when the domains are equal, along with safety, reflexivity, symmetry, transitivity, uniqueness and the fixed examples. It hasn't been compiled here because there was no Lean toolchain in this session.
