/-!
# Safe firmware update (rollback protection)

MIT 6.858 Lecture 18: IoT Security.
Accept a firmware update only if `newVersion > currentVersion`.
-/

namespace SafeUpdate

/-- Return `true` iff `newVersion` is strictly greater than `currentVersion`.
Both arguments may be negative integers. This function only compares version numbers. -/
def safeUpdateAccept (newVersion currentVersion : Int) : Bool :=
  decide (newVersion > currentVersion)

/-- Run the fixed examples from the Python `check` function. -/
def check (candidate : Int → Int → Bool) : Bool :=
  candidate 5 3 == true &&
  candidate 100 1 == true &&
  candidate 2 1 == true &&
  candidate 3 3 == false &&
  candidate 0 10 == false

/-- The Python `assert check(safe_update_accept)`, checked at compile time. -/
theorem check_safeUpdateAccept : check safeUpdateAccept = true := by decide

#eval if check safeUpdateAccept then "All tests passed." else "FAILED"

/-! ## Concrete examples (including negative versions) -/

example : safeUpdateAccept 5 3 = true := by decide
example : safeUpdateAccept 3 3 = false := by decide
example : safeUpdateAccept 0 10 = false := by decide
example : safeUpdateAccept (-1) (-5) = true := by decide
example : safeUpdateAccept (-5) (-1) = false := by decide

/-! ## Specification -/

/-- An update is accepted exactly when the new version is strictly greater. -/
theorem accept_iff (n c : Int) : safeUpdateAccept n c = true ↔ c < n := by
  unfold safeUpdateAccept
  constructor
  · intro h
    exact of_decide_eq_true h
  · intro h
    exact decide_eq_true h

/-- An update is rejected exactly when the new version is not strictly greater. -/
theorem accept_eq_false_iff (n c : Int) : safeUpdateAccept n c = false ↔ n ≤ c := by
  unfold safeUpdateAccept
  constructor
  · intro h
    have h' : ¬ (n > c) := of_decide_eq_false h
    omega
  · intro h
    exact decide_eq_false (by omega)

/-! ## Rollback and replay properties -/

/-- Reinstalling the current version (a replay) is always rejected. -/
theorem reject_same_version (v : Int) : safeUpdateAccept v v = false :=
  (accept_eq_false_iff v v).mpr (Int.le_refl v)

/-- Any older version (a rollback) is always rejected. -/
theorem reject_older {n c : Int} (h : n < c) : safeUpdateAccept n c = false :=
  (accept_eq_false_iff n c).mpr (by omega)

/-- Asymmetry: if `a` may replace `b`, then `b` may never replace `a`. -/
theorem accept_asymm (a b : Int) (h : safeUpdateAccept a b = true) :
    safeUpdateAccept b a = false := by
  have h1 := (accept_iff a b).mp h
  exact (accept_eq_false_iff b a).mpr (by omega)

/-- Transitivity: a chain of accepted updates `a → b → c` means `c` replaces `a` too. -/
theorem accept_trans {a b c : Int}
    (h₁ : safeUpdateAccept b a = true) (h₂ : safeUpdateAccept c b = true) :
    safeUpdateAccept c a = true := by
  have hab := (accept_iff b a).mp h₁
  have hbc := (accept_iff c b).mp h₂
  exact (accept_iff c a).mpr (by omega)

/-! ## Device state model -/

/-- The installed version after attempting one update. -/
def applyUpdate (current new : Int) : Int :=
  if safeUpdateAccept new current then new else current

/-- The installed version after attempting a sequence of updates in order. -/
def applyUpdates (current : Int) : List Int → Int
  | [] => current
  | v :: vs => applyUpdates (applyUpdate current v) vs

theorem applyUpdate_of_accept {current new : Int}
    (h : safeUpdateAccept new current = true) :
    applyUpdate current new = new := by
  simp [applyUpdate, h]

theorem applyUpdate_of_reject {current new : Int}
    (h : safeUpdateAccept new current = false) :
    applyUpdate current new = current := by
  simp [applyUpdate, h]

/-- A single update attempt never lowers the installed version. -/
theorem applyUpdate_ge (current new : Int) : current ≤ applyUpdate current new := by
  cases hacc : safeUpdateAccept new current with
  | true =>
    rw [applyUpdate_of_accept hacc]
    have := (accept_iff new current).mp hacc
    omega
  | false =>
    rw [applyUpdate_of_reject hacc]
    exact Int.le_refl current

/-- If an update attempt changes the installed version, it strictly increases it. -/
theorem applyUpdate_changes_only_upward (current new : Int)
    (h : applyUpdate current new ≠ current) :
    current < applyUpdate current new := by
  cases hacc : safeUpdateAccept new current with
  | true =>
    rw [applyUpdate_of_accept hacc]
    exact (accept_iff new current).mp hacc
  | false =>
    exact absurd (applyUpdate_of_reject hacc) h

/-- No sequence of update attempts, however adversarial, can roll the device back. -/
theorem applyUpdates_ge (current : Int) (vs : List Int) :
    current ≤ applyUpdates current vs := by
  induction vs generalizing current with
  | nil =>
    show current ≤ current
    omega
  | cons v vs ih =>
    show current ≤ applyUpdates (applyUpdate current v) vs
    have h1 := applyUpdate_ge current v
    have h2 := ih (applyUpdate current v)
    omega

end SafeUpdate

-- TLDR-end: [lean: safe firmware update] Lean 4 port of `safe_update_accept` and `check`,
-- with theorems for the specification, replay and rollback rejection, asymmetry, transitivity,
-- and monotonicity over any sequence of updates. Not compiled here: no Lean toolchain was
-- available in this session.
