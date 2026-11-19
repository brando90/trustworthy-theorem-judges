import Mathlib
namespace Agent

/-!
# Safe privilege dropping

A translation of the privilege-management decision procedure from MIT 6.858
Lecture 5 (OKWS). An invalid target UID of zero is rejected first. Otherwise,
root drops to the target after initialization; every other call keeps its UID.

`Int` models Python's arbitrary-precision integers, including negative inputs.
`Option Int` models `int | None`. This file models the decision procedure, not
an operating-system call: no positivity or successful-system-call assumption is
silently added. The theorems cover every integer input and both Boolean values.
-/

namespace UnsafePrivilegeDropSafe

/-! ## Functional implementation -/

/-- Apply the Python checks in their original priority order. -/
def safe_privilege_drop (current_uid : Int) (init_done : Bool)
    (target_uid : Int) : Option Int :=
  if target_uid = 0 then
    none
  else if init_done = true ∧ current_uid = 0 then
    some target_uid
  else
    some current_uid

/-! ## Unit tests: all eight assertions from the Python `check` -/

example : safe_privilege_drop 0 true 1000 = some 1000 := by native_decide
example : safe_privilege_drop 0 false 1000 = some 0 := by native_decide
example : safe_privilege_drop 500 true 1000 = some 500 := by native_decide
example : safe_privilege_drop 500 false 1000 = some 500 := by native_decide
example : safe_privilege_drop 0 true 33 = some 33 := by native_decide
example : safe_privilege_drop 0 true 65534 = some 65534 := by native_decide
example : safe_privilege_drop 0 true 0 = none := by native_decide
example : safe_privilege_drop 0 false 0 = none := by native_decide

/-- The executable counterpart of the Python test harness. -/
def check (candidate : Int → Bool → Int → Option Int) : Bool :=
  (candidate 0 true 1000 == some 1000) &&
  (candidate 0 false 1000 == some 0) &&
  (candidate 500 true 1000 == some 500) &&
  (candidate 500 false 1000 == some 500) &&
  (candidate 0 true 33 == some 33) &&
  (candidate 0 true 65534 == some 65534) &&
  (candidate 0 true 0 == none) &&
  (candidate 0 false 0 == none)

example : check safe_privilege_drop = true := by native_decide
#eval check safe_privilege_drop
#eval safe_privilege_drop 0 true 1000
#eval safe_privilege_drop 0 false 1000
#eval safe_privilege_drop 0 true 0

-- Rejection also takes precedence for non-root callers.
example : safe_privilege_drop 500 true 0 = none := by native_decide
example : safe_privilege_drop 500 false 0 = none := by native_decide
-- Python does not reject negative integers; the translation does not either.
example : safe_privilege_drop 0 true (-7) = some (-7) := by native_decide
example : safe_privilege_drop (-7) true 1000 = some (-7) := by native_decide

/-! ## Precondition -/

/-- Every well-typed input is admissible, including target zero and negative UIDs. -/
def Pre (_current_uid : Int) (_init_done : Bool) (_target_uid : Int) : Prop :=
  True

/-! ## Properties and kernel-checked proofs -/

/-- Invalid targets are rejected, and these are the only failures. -/
def invalid_target_prop (current_uid : Int) (init_done : Bool)
    (target_uid : Int) : Prop :=
  safe_privilege_drop current_uid init_done target_uid = none ↔ target_uid = 0

theorem invalid_target_thm (current_uid : Int) (init_done : Bool)
    (target_uid : Int) : invalid_target_prop current_uid init_done target_uid := by
  by_cases ht : target_uid = 0 <;>
    by_cases hd : init_done = true ∧ current_uid = 0 <;>
    simp [invalid_target_prop, safe_privilege_drop, ht, hd]

/-- Root drops to any nonzero target once initialization has completed. -/
def drop_after_init_prop (current_uid : Int) (init_done : Bool)
    (target_uid : Int) : Prop :=
  target_uid ≠ 0 → init_done = true → current_uid = 0 →
    safe_privilege_drop current_uid init_done target_uid = some target_uid

theorem drop_after_init_thm (current_uid : Int) (init_done : Bool)
    (target_uid : Int) : drop_after_init_prop current_uid init_done target_uid := by
  unfold drop_after_init_prop
  intro ht hb hc
  simp [safe_privilege_drop, ht, hb, hc]

/-- Before initialization, a valid request leaves the UID unchanged. -/
def keep_before_init_prop (current_uid : Int) (init_done : Bool)
    (target_uid : Int) : Prop :=
  target_uid ≠ 0 → init_done = false →
    safe_privilege_drop current_uid init_done target_uid = some current_uid

theorem keep_before_init_thm (current_uid : Int) (init_done : Bool)
    (target_uid : Int) : keep_before_init_prop current_uid init_done target_uid := by
  unfold keep_before_init_prop
  intro ht hb
  simp [safe_privilege_drop, ht, hb]

/-- Non-root callers keep their UID, unless the target is invalid. -/
def nonroot_unchanged_prop (current_uid : Int) (init_done : Bool)
    (target_uid : Int) : Prop :=
  target_uid ≠ 0 → current_uid ≠ 0 →
    safe_privilege_drop current_uid init_done target_uid = some current_uid

theorem nonroot_unchanged_thm (current_uid : Int) (init_done : Bool)
    (target_uid : Int) : nonroot_unchanged_prop current_uid init_done target_uid := by
  unfold nonroot_unchanged_prop
  intro ht hc
  simp [safe_privilege_drop, ht, hc]

/-- After initialization the result is never a successful root UID.
An invalid target still returns `none`, so no target precondition is needed. -/
def least_privilege_prop (current_uid : Int) (init_done : Bool)
    (target_uid : Int) : Prop :=
  init_done = true → safe_privilege_drop current_uid init_done target_uid ≠ some 0

theorem least_privilege_thm (current_uid : Int) (init_done : Bool)
    (target_uid : Int) : least_privilege_prop current_uid init_done target_uid := by
  unfold least_privilege_prop
  intro hb
  by_cases ht : target_uid = 0 <;> by_cases hc : current_uid = 0 <;>
    simp [safe_privilege_drop, hb, ht, hc]

/-- Root is returned exactly when root is still initializing with a valid target.
This also rules out escalation of a non-root caller to root. -/
def root_retained_iff_prop (current_uid : Int) (init_done : Bool)
    (target_uid : Int) : Prop :=
  safe_privilege_drop current_uid init_done target_uid = some 0 ↔
    target_uid ≠ 0 ∧ init_done = false ∧ current_uid = 0

theorem root_retained_iff_thm (current_uid : Int) (init_done : Bool)
    (target_uid : Int) : root_retained_iff_prop current_uid init_done target_uid := by
  cases init_done <;> by_cases ht : target_uid = 0 <;>
    by_cases hc : current_uid = 0 <;>
    simp [root_retained_iff_prop, safe_privilege_drop, ht, hc]

/-! ## Postcondition -/

/-- Complete branch behavior together with the least-privilege guarantees. -/
def Post_prop (current_uid : Int) (init_done : Bool) (target_uid : Int) : Prop :=
  invalid_target_prop current_uid init_done target_uid ∧
  drop_after_init_prop current_uid init_done target_uid ∧
  keep_before_init_prop current_uid init_done target_uid ∧
  nonroot_unchanged_prop current_uid init_done target_uid ∧
  least_privilege_prop current_uid init_done target_uid ∧
  root_retained_iff_prop current_uid init_done target_uid

/-! ## Bounded property-based tests

Each test below checks the executable form of the named property on the whole
Cartesian product of two UID samples and both initialization states: 2048
triples per property. The samples include every integer from -12 through 12,
root, and the larger UIDs used by the original tests. These finite tests are
only evidence; none of the universal proofs above depends on them.
-/

def uidSamples : List Int :=
  (List.range 25).map (fun n => (n : Int) - 12) ++
    [-65534, -1000, -33, 33, 500, 1000, 65534]

def testUidGrid (p : Int → Bool → Int → Bool) : Bool :=
  uidSamples.all (fun current_uid =>
    [false, true].all (fun init_done =>
      uidSamples.all (fun target_uid => p current_uid init_done target_uid)))

-- PBT for invalid_target_prop: rejection is exactly target zero.
example : testUidGrid (fun c b t =>
    decide (safe_privilege_drop c b t = none ↔ t = 0)) = true := by
  native_decide

-- PBT for drop_after_init_prop; both guards are included explicitly.
example : testUidGrid (fun c b t =>
    decide (t ≠ 0 → b = true → c = 0 →
      safe_privilege_drop c b t = some t)) = true := by
  native_decide

-- PBT for keep_before_init_prop.
example : testUidGrid (fun c b t =>
    decide (t ≠ 0 → b = false →
      safe_privilege_drop c b t = some c)) = true := by
  native_decide

-- PBT for nonroot_unchanged_prop, including negative non-root UIDs.
example : testUidGrid (fun c b t =>
    decide (t ≠ 0 → c ≠ 0 →
      safe_privilege_drop c b t = some c)) = true := by
  native_decide

-- PBT for least_privilege_prop, including invalid targets.
example : testUidGrid (fun c b t =>
    decide (b = true → safe_privilege_drop c b t ≠ some 0)) = true := by
  native_decide

-- PBT for root_retained_iff_prop, testing both directions.
example : testUidGrid (fun c b t =>
    decide (safe_privilege_drop c b t = some 0 ↔
      t ≠ 0 ∧ b = false ∧ c = 0)) = true := by
  native_decide

/-- Executable form of the full postcondition, without needing instances for
our proposition-valued specification definitions. -/
def post_check (c : Int) (b : Bool) (t : Int) : Bool :=
  let result := safe_privilege_drop c b t
  decide (
    (result = none ↔ t = 0) ∧
    (t ≠ 0 → b = true → c = 0 → result = some t) ∧
    (t ≠ 0 → b = false → result = some c) ∧
    (t ≠ 0 → c ≠ 0 → result = some c) ∧
    (b = true → result ≠ some 0) ∧
    (result = some 0 ↔ t ≠ 0 ∧ b = false ∧ c = 0))

-- PBT for Post_prop: check all conjuncts together on every sampled input.
example : testUidGrid post_check = true := by native_decide
#eval testUidGrid post_check

/-! ## Correctness -/

theorem correctness_thm (current_uid : Int) (init_done : Bool) (target_uid : Int) :
    Pre current_uid init_done target_uid →
      Post_prop current_uid init_done target_uid := by
  intro _
  exact ⟨invalid_target_thm current_uid init_done target_uid,
    drop_after_init_thm current_uid init_done target_uid,
    keep_before_init_thm current_uid init_done target_uid,
    nonroot_unchanged_thm current_uid init_done target_uid,
    least_privilege_thm current_uid init_done target_uid,
    root_retained_iff_thm current_uid init_done target_uid⟩

/-! ## Imperative implementation -/

/-- An early rejection followed by a possible mutation of the effective UID. -/
def safe_privilege_drop_imp (current_uid : Int) (init_done : Bool)
    (target_uid : Int) : Option Int := Id.run do
  let mut uid := current_uid
  if target_uid = 0 then
    return none
  if init_done = true ∧ uid = 0 then
    uid := target_uid
  return some uid

/-! ## Imperative tests -/

example : safe_privilege_drop_imp 0 true 1000 = some 1000 := by native_decide
example : safe_privilege_drop_imp 0 false 1000 = some 0 := by native_decide
example : safe_privilege_drop_imp 500 true 1000 = some 500 := by native_decide
example : safe_privilege_drop_imp 500 false 1000 = some 500 := by native_decide
example : safe_privilege_drop_imp 0 true 33 = some 33 := by native_decide
example : safe_privilege_drop_imp 0 true 65534 = some 65534 := by native_decide
example : safe_privilege_drop_imp 0 true 0 = none := by native_decide
example : safe_privilege_drop_imp 0 false 0 = none := by native_decide
example : safe_privilege_drop_imp 500 true 0 = none := by native_decide
example : safe_privilege_drop_imp 500 false 0 = none := by native_decide
example : safe_privilege_drop_imp 0 true (-7) = some (-7) := by native_decide
example : safe_privilege_drop_imp (-7) true 1000 = some (-7) := by native_decide
example : check safe_privilege_drop_imp = true := by native_decide
#eval check safe_privilege_drop_imp
#eval safe_privilege_drop_imp 0 true 33
#eval safe_privilege_drop_imp 500 true 0

-- Additional bounded regression check of both implementations together.
example : testUidGrid (fun c b t =>
    decide (safe_privilege_drop c b t = safe_privilege_drop_imp c b t)) = true := by
  native_decide

/-! ## Functional / imperative equivalence -/

theorem functional_eq_imperative_thm (current_uid : Int) (init_done : Bool)
    (target_uid : Int) :
    safe_privilege_drop current_uid init_done target_uid =
      safe_privilege_drop_imp current_uid init_done target_uid := by
  by_cases ht : target_uid = 0 <;>
    by_cases hd : init_done = true ∧ current_uid = 0 <;>
    simp [safe_privilege_drop, safe_privilege_drop_imp, ht, hd]

end UnsafePrivilegeDropSafe
end Agent
