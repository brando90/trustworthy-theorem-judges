/-!
# Safe seccomp filter

Permit the system call only if `syscallId` is in the `allowed` whitelist.
Teaching model for MIT 6.858.

This is a Lean 4 translation of `safe_seccomp_filter` and `check`, using only Lean core
(no Mathlib). Python types map as follows:

* `int` becomes `Int`, because Python integers are unbounded.
* `list[int]` becomes `List Int`.
* `bool` becomes `Bool`.
* `Callable` becomes `Int → List Int → Bool`.

The filter is a pure function. It computes a whitelist decision and does not
execute or block a system call.
-/

namespace SafeSeccomp

/-- Return `true` exactly when `syscallId` occurs in `allowed`, and `false` otherwise.
An empty list returns `false`. This mirrors Python's `syscall_id in allowed`:
it scans the list from left to right and compares each element with `==`. -/
def safeSeccompFilter (syscallId : Int) : List Int → Bool
  | [] => false
  | a :: rest => syscallId == a || safeSeccompFilter syscallId rest

/-- Run the fixed examples and return `true` exactly when all of them pass.
The Python version raises `AssertionError` on a mismatch. This version returns `false`. -/
def check (candidate : Int → List Int → Bool) : Bool :=
  candidate 1 [1, 2, 3, 60] == true &&
  candidate 60 [1, 2, 3, 60] == true &&
  candidate 101 [1, 2, 3, 60] == false &&
  candidate 0 [1, 2, 3, 60] == false &&
  candidate 1 [] == false

/-! ## Helper -/

/-- Two booleans are equal when each is `true` exactly when the other is. -/
theorem decision_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b
  · rfl
  · exact h.mpr rfl
  · exact absurd (h.mp rfl) (by decide)
  · rfl

/-! ## Unfolding equations -/

/-- Fail closed: an empty whitelist denies every system call. -/
theorem safeSeccompFilter_nil (x : Int) : safeSeccompFilter x [] = false := rfl

theorem safeSeccompFilter_cons (x a : Int) (l : List Int) :
    safeSeccompFilter x (a :: l) = (x == a || safeSeccompFilter x l) := rfl

/-! ## Specification: the filter permits exactly the members of the whitelist -/

/-- Main correctness theorem: a call is permitted exactly when its ID is in the whitelist. -/
theorem safeSeccompFilter_iff_mem (x : Int) (l : List Int) :
    safeSeccompFilter x l = true ↔ x ∈ l := by
  induction l with
  | nil => simp [safeSeccompFilter]
  | cons a rest ih => simp [safeSeccompFilter, ih]

/-- A call is denied exactly when its ID is missing from the whitelist. -/
theorem safeSeccompFilter_eq_false_iff (x : Int) (l : List Int) :
    safeSeccompFilter x l = false ↔ x ∉ l := by
  constructor
  · intro hf hmem
    have ht := (safeSeccompFilter_iff_mem x l).mpr hmem
    rw [hf] at ht
    exact absurd ht (by decide)
  · intro hnot
    cases hb : safeSeccompFilter x l with
    | false => rfl
    | true => exact absurd ((safeSeccompFilter_iff_mem x l).mp hb) hnot

/-- Soundness: a permitted call is always on the whitelist. -/
theorem mem_of_safeSeccompFilter {x : Int} {l : List Int}
    (h : safeSeccompFilter x l = true) : x ∈ l :=
  (safeSeccompFilter_iff_mem x l).mp h

/-- Completeness: every whitelisted call is permitted. -/
theorem safeSeccompFilter_of_mem {x : Int} {l : List Int} (h : x ∈ l) :
    safeSeccompFilter x l = true :=
  (safeSeccompFilter_iff_mem x l).mpr h

/-- Default deny: a call that is not whitelisted is rejected. -/
theorem safeSeccompFilter_of_not_mem {x : Int} {l : List Int} (h : x ∉ l) :
    safeSeccompFilter x l = false :=
  (safeSeccompFilter_eq_false_iff x l).mpr h

/-- The filter is the decision procedure for list membership, like Python's `in`. -/
theorem safeSeccompFilter_eq_decide (x : Int) (l : List Int) :
    safeSeccompFilter x l = decide (x ∈ l) :=
  decision_ext (by simp [safeSeccompFilter_iff_mem])

/-- A one-entry whitelist permits exactly that system call. -/
theorem safeSeccompFilter_singleton_iff (x y : Int) :
    safeSeccompFilter x [y] = true ↔ x = y := by
  rw [safeSeccompFilter_iff_mem]
  simp

theorem safeSeccompFilter_self_cons (x : Int) (l : List Int) :
    safeSeccompFilter x (x :: l) = true := by
  rw [safeSeccompFilter_iff_mem]
  simp

/-! ## Structural properties of the whitelist -/

/-- The decision depends only on which IDs the whitelist contains. -/
theorem safeSeccompFilter_congr {l₁ l₂ : List Int} (h : ∀ y, y ∈ l₁ ↔ y ∈ l₂) (x : Int) :
    safeSeccompFilter x l₁ = safeSeccompFilter x l₂ :=
  decision_ext <|
    (safeSeccompFilter_iff_mem x l₁).trans ((h x).trans (safeSeccompFilter_iff_mem x l₂).symm)

/-- Monotonicity: widening the whitelist never revokes a permission. -/
theorem safeSeccompFilter_mono {l₁ l₂ : List Int} (hsub : ∀ y, y ∈ l₁ → y ∈ l₂) {x : Int}
    (h : safeSeccompFilter x l₁ = true) : safeSeccompFilter x l₂ = true :=
  (safeSeccompFilter_iff_mem x l₂).mpr (hsub x ((safeSeccompFilter_iff_mem x l₁).mp h))

theorem safeSeccompFilter_cons_of_true {x : Int} {l : List Int} (y : Int)
    (h : safeSeccompFilter x l = true) : safeSeccompFilter x (y :: l) = true :=
  safeSeccompFilter_mono (fun z hz => by simp [hz]) h

/-- Concatenating two whitelists permits a call that either of them permits. -/
theorem safeSeccompFilter_append (x : Int) (l₁ l₂ : List Int) :
    safeSeccompFilter x (l₁ ++ l₂) = (safeSeccompFilter x l₁ || safeSeccompFilter x l₂) := by
  induction l₁ with
  | nil => rfl
  | cons a rest ih =>
    show (x == a || safeSeccompFilter x (rest ++ l₂)) =
      ((x == a || safeSeccompFilter x rest) || safeSeccompFilter x l₂)
    rw [ih]
    cases x == a <;> rfl

/-- The order in which two whitelist fragments are joined does not matter. -/
theorem safeSeccompFilter_append_comm (x : Int) (l₁ l₂ : List Int) :
    safeSeccompFilter x (l₁ ++ l₂) = safeSeccompFilter x (l₂ ++ l₁) := by
  rw [safeSeccompFilter_append, safeSeccompFilter_append, Bool.or_comm]

/-- Reversing the whitelist does not change any decision. -/
theorem safeSeccompFilter_reverse (x : Int) (l : List Int) :
    safeSeccompFilter x l.reverse = safeSeccompFilter x l :=
  safeSeccompFilter_congr (fun _ => by simp) x

/-- Duplicate whitelist entries do not change any decision. -/
theorem safeSeccompFilter_dup_head (x y : Int) (l : List Int) :
    safeSeccompFilter x (y :: y :: l) = safeSeccompFilter x (y :: l) := by
  show (x == y || (x == y || safeSeccompFilter x l)) = (x == y || safeSeccompFilter x l)
  cases x == y <;> rfl

/-! ## Filtering a trace of system calls -/

/-- A call survives filtering exactly when it is in the trace and on the whitelist. -/
theorem mem_filter_trace_iff (trace allowed : List Int) (x : Int) :
    x ∈ trace.filter (fun s => safeSeccompFilter s allowed) ↔ x ∈ trace ∧ x ∈ allowed := by
  simp [List.mem_filter, safeSeccompFilter_iff_mem]

/-- Security property: every call that passes the filter is whitelisted. -/
theorem filter_trace_sound (trace allowed : List Int) :
    ∀ x ∈ trace.filter (fun s => safeSeccompFilter s allowed), x ∈ allowed :=
  fun x hx => ((mem_filter_trace_iff trace allowed x).mp hx).2

/-! ## The fixed examples from `check` -/

theorem test_allows_first : safeSeccompFilter 1 [1, 2, 3, 60] = true := by decide
theorem test_allows_last : safeSeccompFilter 60 [1, 2, 3, 60] = true := by decide
theorem test_denies_absent : safeSeccompFilter 101 [1, 2, 3, 60] = false := by decide
theorem test_denies_zero : safeSeccompFilter 0 [1, 2, 3, 60] = false := by decide
theorem test_denies_empty : safeSeccompFilter 1 [] = false := by decide

/-- The implementation passes the test suite. -/
theorem check_safeSeccompFilter : check safeSeccompFilter = true := by decide

/-- Every candidate that meets the specification passes the test suite. -/
theorem check_of_spec (candidate : Int → List Int → Bool)
    (h : ∀ x l, candidate x l = true ↔ x ∈ l) : check candidate = true := by
  have hc : candidate = safeSeccompFilter := by
    funext x l
    exact decision_ext ((h x l).trans (safeSeccompFilter_iff_mem x l).symm)
  subst hc
  exact check_safeSeccompFilter

/-- The test suite rejects a filter that permits everything. -/
theorem check_rejects_allow_all : check (fun _ _ => true) = false := by decide

/-- The test suite rejects a filter that denies everything. -/
theorem check_rejects_deny_all : check (fun _ _ => false) = false := by decide

/-- The test suite rejects a filter that ignores the last whitelist entry. -/
theorem check_rejects_drop_last :
    check (fun x l => safeSeccompFilter x l.dropLast) = false := by decide

end SafeSeccomp

/-- Counterpart of Python's `if __name__ == "__main__":` block. -/
def main : IO Unit := do
  if SafeSeccomp.check SafeSeccomp.safeSeccompFilter then
    IO.println "All tests passed."
  else
    throw <| IO.userError "Failed: SafeSeccomp"

-- TL;DR: Lean 4 version of the seccomp filter and check, using only Lean core. It proves that
-- the filter permits exactly the whitelisted IDs, denies by default, ignores order and
-- duplicates, and passes and properly checks the test suite. No Lean toolchain was
-- available in this session, so the file has not been compiled.
