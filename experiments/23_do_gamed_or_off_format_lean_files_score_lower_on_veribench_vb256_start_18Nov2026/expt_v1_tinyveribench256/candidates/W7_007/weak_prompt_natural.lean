/-!
# Unsafe DB proxy

This is a Lean 4 translation of the Python `unsafe_query_check`. The function
approves every request without checking the whitelist, which allows one service
to read another service's data.

The file also defines a whitelist-respecting `safeQueryCheck` for comparison.
The theorems state the flaw formally: the unsafe check approves requests that
are not in the whitelist.
-/

namespace UnsafeDbProxy

/-- A whitelist is a list of allowed `(service_id, query_type)` pairs. -/
abbrev Whitelist := List (Int × Int)

/-- Approve the request without checking whether `(serviceId, queryType)` is in `whitelist`. -/
def unsafeQueryCheck (_serviceId : Int) (_queryType : Int) (_whitelist : Whitelist) : Bool :=
  true

/-- Reference version: approve only if `(serviceId, queryType)` appears in `whitelist`. -/
def safeQueryCheck (serviceId queryType : Int) (whitelist : Whitelist) : Bool :=
  whitelist.any (fun p => p.1 == serviceId && p.2 == queryType)

/-! ## The fixed examples from `check()` -/

example : unsafeQueryCheck 1 10 [(1, 10), (2, 20)] = true := rfl
example : unsafeQueryCheck 3 99 [(1, 10), (2, 20)] = true := rfl
example : unsafeQueryCheck 0 0 [] = true := rfl
example : unsafeQueryCheck 1 0 [] = true := rfl
example : unsafeQueryCheck 1 1 [(1, 10)] = true := rfl

/-- Translation of the Python `check()`: `true` exactly when every fixed example holds. -/
def check : Bool :=
  unsafeQueryCheck 1 10 [(1, 10), (2, 20)] == true &&
  unsafeQueryCheck 3 99 [(1, 10), (2, 20)] == true &&
  unsafeQueryCheck 0 0 [] == true &&
  unsafeQueryCheck 1 0 [] == true &&
  unsafeQueryCheck 1 1 [(1, 10)] == true

theorem check_passes : check = true := by decide

/-- Translation of `if __name__ == "__main__": check()`. -/
def main : IO Unit := do
  unless check do
    throw <| IO.userError "AssertionError: check failed"

/-! ## Properties of the unsafe check -/

/-- The unsafe check approves every request. -/
theorem unsafe_always_true (s q : Int) (w : Whitelist) :
    unsafeQueryCheck s q w = true := rfl

/-- The unsafe check is the constant `true` function. -/
theorem unsafe_eq_const : unsafeQueryCheck = fun _ _ _ => true := rfl

/-- The result does not depend on the whitelist at all. -/
theorem unsafe_ignores_whitelist (s q : Int) (w₁ w₂ : Whitelist) :
    unsafeQueryCheck s q w₁ = unsafeQueryCheck s q w₂ := rfl

/-- The result does not depend on the service or query either. -/
theorem unsafe_ignores_request (s₁ q₁ s₂ q₂ : Int) (w : Whitelist) :
    unsafeQueryCheck s₁ q₁ w = unsafeQueryCheck s₂ q₂ w := rfl

/-- An empty whitelist, which should deny everything, still approves every request. -/
theorem unsafe_approves_with_empty_whitelist (s q : Int) :
    unsafeQueryCheck s q [] = true := rfl

/-- The flaw: requests that are not in the whitelist are still approved. -/
theorem unsafe_approves_unlisted (s q : Int) (w : Whitelist) (_h : (s, q) ∉ w) :
    unsafeQueryCheck s q w = true := rfl

/-- The unsafe check is not sound: approval does not imply whitelist membership. -/
theorem unsafe_not_sound :
    ¬ ∀ (s q : Int) (w : Whitelist), unsafeQueryCheck s q w = true → (s, q) ∈ w := by
  intro h
  have hmem := h 0 0 [] rfl
  simp at hmem

/-! ## Properties of the safe reference check -/

/-- Soundness: the safe check approves only whitelisted pairs. -/
theorem safe_sound (s q : Int) (w : Whitelist) (h : safeQueryCheck s q w = true) :
    (s, q) ∈ w := by
  unfold safeQueryCheck at h
  rw [List.any_eq_true] at h
  obtain ⟨⟨a, b⟩, hmem, hab⟩ := h
  simp at hab
  obtain ⟨rfl, rfl⟩ := hab
  exact hmem

/-- Completeness: the safe check approves every whitelisted pair. -/
theorem safe_complete (s q : Int) (w : Whitelist) (h : (s, q) ∈ w) :
    safeQueryCheck s q w = true := by
  unfold safeQueryCheck
  rw [List.any_eq_true]
  exact ⟨(s, q), h, by simp⟩

/-- The safe check is exactly whitelist membership. -/
theorem safe_iff_mem (s q : Int) (w : Whitelist) :
    safeQueryCheck s q w = true ↔ (s, q) ∈ w :=
  ⟨safe_sound s q w, safe_complete s q w⟩

/-- An empty whitelist makes the safe check deny everything. -/
theorem safe_denies_with_empty_whitelist (s q : Int) :
    safeQueryCheck s q [] = false := rfl

/-! ## Comparing the two checks -/

/-- The unsafe check approves everything the safe check approves (and more). -/
theorem safe_implies_unsafe (s q : Int) (w : Whitelist) :
    safeQueryCheck s q w = true → unsafeQueryCheck s q w = true :=
  fun _ => rfl

/-- A concrete cross-service request from `check()` that the safe check rejects
and the unsafe check approves. -/
theorem unsafe_bypasses_whitelist :
    ∃ (s q : Int) (w : Whitelist),
      safeQueryCheck s q w = false ∧ unsafeQueryCheck s q w = true :=
  ⟨3, 99, [(1, 10), (2, 20)], by decide, rfl⟩

/-- The two checks are different functions. -/
theorem unsafe_ne_safe : unsafeQueryCheck ≠ safeQueryCheck := by
  intro h
  have := congrFun (congrFun (congrFun h 0) 0) []
  simp [unsafeQueryCheck, safeQueryCheck] at this

end UnsafeDbProxy

-- TL;DR: `unsafeQueryCheck` is the constant `true` function. The theorems show it
-- ignores the whitelist, and the comparison with `safeQueryCheck` proves it bypasses
-- the whitelist. This file was not compiled here.
