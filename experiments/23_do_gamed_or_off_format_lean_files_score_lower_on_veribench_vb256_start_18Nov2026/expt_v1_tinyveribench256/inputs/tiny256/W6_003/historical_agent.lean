import Mathlib
namespace Agent

/-!
# Unsafe privilege management

Translation of the MIT 6.858 / OKWS example: startup returns the current UID
without calling `setuid`, even when privileged initialization is complete.
Thus a root process remains root. This file specifies the vulnerable behavior,
not the desirable policy of dropping privileges after binding port 80.

Python's arbitrary-precision integers are represented by `Int`. No restriction
to nonnegative or machine-sized UIDs is imposed. The flag is deliberately ignored.
-/

namespace UnsafePrivilegeDrop

/-! ## Functional implementation and the Python assertion checker -/

def unsafe_privilege_drop (current_uid : Int) (_init_done : Bool) : Int :=
  current_uid

def check (candidate : Int → Bool → Int) : Bool :=
  (candidate 0 true == 0) &&
  (candidate 0 false == 0) &&
  (candidate 1000 true == 1000) &&
  (candidate 1000 false == 1000) &&
  (candidate 500 true == 500) &&
  (candidate 33 false == 33)

/-! ## Fixed unit tests -/

example : unsafe_privilege_drop 0 true = 0 := by native_decide
example : unsafe_privilege_drop 0 false = 0 := by native_decide
example : unsafe_privilege_drop 1000 true = 1000 := by native_decide
example : unsafe_privilege_drop 1000 false = 1000 := by native_decide
example : unsafe_privilege_drop 500 true = 500 := by native_decide
example : unsafe_privilege_drop 33 false = 33 := by native_decide
example : unsafe_privilege_drop (-7) true = -7 := by native_decide
example : check unsafe_privilege_drop = true := by native_decide

#eval unsafe_privilege_drop 0 true
#eval check unsafe_privilege_drop
#eval if check unsafe_privilege_drop then "All tests passed."
      else "Candidate failed privilege drop tests"

/-! ## Preconditions and semantic properties -/

/-- The Python implementation accepts every integer and either Boolean flag. -/
def Pre (_current_uid : Int) (_init_done : Bool) : Prop := True

/-- The complete input/output behavior: the UID is unchanged. -/
def uid_unchanged_prop (current_uid : Int) (init_done : Bool) : Prop :=
  unsafe_privilege_drop current_uid init_done = current_uid

theorem uid_unchanged_thm (current_uid : Int) (init_done : Bool) :
    uid_unchanged_prop current_uid init_done := by
  rfl

/-- Neither changing nor keeping the initialization flag changes the result. -/
def flag_ignored_prop (current_uid : Int) : Prop :=
  ∀ first second : Bool,
    unsafe_privilege_drop current_uid first =
      unsafe_privilege_drop current_uid second

theorem flag_ignored_thm (current_uid : Int) :
    flag_ignored_prop current_uid := by
  intro first second
  rfl

/-- In particular, completion of initialization does not remove root access. -/
def root_retained_prop (current_uid : Int) (init_done : Bool) : Prop :=
  current_uid = 0 → unsafe_privilege_drop current_uid init_done = 0

theorem root_retained_thm (current_uid : Int) (init_done : Bool) :
    root_retained_prop current_uid init_done := by
  intro h
  exact h

/-- Non-root UIDs are also left unchanged, for both values of the flag. -/
def nonroot_unchanged_prop (current_uid : Int) (init_done : Bool) : Prop :=
  current_uid ≠ 0 → unsafe_privilege_drop current_uid init_done = current_uid

theorem nonroot_unchanged_thm (current_uid : Int) (init_done : Bool) :
    nonroot_unchanged_prop current_uid init_done := by
  intro _
  rfl

/-- Startup neither grants root to a non-root process nor removes existing root. -/
def root_iff_prop (current_uid : Int) (init_done : Bool) : Prop :=
  unsafe_privilege_drop current_uid init_done = 0 ↔ current_uid = 0

theorem root_iff_thm (current_uid : Int) (init_done : Bool) :
    root_iff_prop current_uid init_done := by
  exact Iff.rfl

/-- The supplied six Python assertions also hold by kernel reduction. -/
theorem check_thm : check unsafe_privilege_drop = true := by
  decide

/-! ## Postcondition -/

def Post_prop (current_uid : Int) (init_done : Bool) : Prop :=
  uid_unchanged_prop current_uid init_done ∧
  flag_ignored_prop current_uid ∧
  root_retained_prop current_uid init_done ∧
  nonroot_unchanged_prop current_uid init_done ∧
  root_iff_prop current_uid init_done

/-! ## Property-based tests

These are executable Boolean checks, not proofs of the universal theorems.
The bounded suite exhausts UIDs -64 through 64 and both flags, and additionally
checks representative large positive/negative values and the source examples.
These test bounds do not restrict `Pre` or any theorem's input domain.
-/

private def uidSamples : List Int :=
  (List.range 129).map (fun n => (n : Int) - 64) ++
    [500, 1000, 2147483647, -2147483648,
     1000000000000000000000000000000, -1000000000000000000000000000000]

private def flagSamples : List Bool := [false, true]

-- PBT for uid_unchanged_prop.
example : uidSamples.all (fun uid => flagSamples.all (fun done =>
    unsafe_privilege_drop uid done == uid)) = true := by
  native_decide

-- PBT for flag_ignored_prop: exhaust every pair of Boolean flags.
example : uidSamples.all (fun uid => flagSamples.all (fun first =>
    flagSamples.all (fun second =>
      unsafe_privilege_drop uid first == unsafe_privilege_drop uid second))) = true := by
  native_decide

-- PBT for root_retained_prop: Boolean form of the implication.
-- Zero occurs in uidSamples, so both non-vacuous root cases are included.
example : uidSamples.all (fun uid => flagSamples.all (fun done =>
    (uid != 0) || (unsafe_privilege_drop uid done == 0))) = true := by
  native_decide

-- PBT for nonroot_unchanged_prop.
example : uidSamples.all (fun uid => flagSamples.all (fun done =>
    (uid == 0) || (unsafe_privilege_drop uid done == uid))) = true := by
  native_decide

-- PBT for root_iff_prop: equality of the two root-status Booleans.
example : uidSamples.all (fun uid => flagSamples.all (fun done =>
    (unsafe_privilege_drop uid done == 0) == (uid == 0))) = true := by
  native_decide

-- PBT for Post_prop: the conjunction of all five executable checks.
example : uidSamples.all (fun uid => flagSamples.all (fun done =>
    (unsafe_privilege_drop uid done == uid) &&
    (flagSamples.all (fun first => flagSamples.all (fun second =>
      unsafe_privilege_drop uid first == unsafe_privilege_drop uid second))) &&
    ((uid != 0) || (unsafe_privilege_drop uid done == 0)) &&
    ((uid == 0) || (unsafe_privilege_drop uid done == uid)) &&
    ((unsafe_privilege_drop uid done == 0) == (uid == 0)))) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (current_uid : Int) (init_done : Bool) :
    Pre current_uid init_done → Post_prop current_uid init_done := by
  intro _
  exact ⟨uid_unchanged_thm current_uid init_done,
    flag_ignored_thm current_uid,
    root_retained_thm current_uid init_done,
    nonroot_unchanged_thm current_uid init_done,
    root_iff_thm current_uid init_done⟩

/-! ## Imperative implementation

The mutable UID undergoes an explicit no-op state transition. There is no
`setuid` operation and, exactly as in the source, the flag is ignored.
-/

def unsafe_privilege_drop_imp (current_uid : Int) (_init_done : Bool) : Int :=
  Id.run do
    let mut uid := current_uid
    uid := uid
    return uid

/-! ## Imperative tests -/

example : unsafe_privilege_drop_imp 0 true = 0 := by native_decide
example : unsafe_privilege_drop_imp 0 false = 0 := by native_decide
example : unsafe_privilege_drop_imp 1000 true = 1000 := by native_decide
example : unsafe_privilege_drop_imp 1000 false = 1000 := by native_decide
example : unsafe_privilege_drop_imp 500 true = 500 := by native_decide
example : unsafe_privilege_drop_imp 33 false = 33 := by native_decide
example : unsafe_privilege_drop_imp (-7) false = -7 := by native_decide
example : check unsafe_privilege_drop_imp = true := by native_decide

#eval unsafe_privilege_drop_imp 0 true
#eval check unsafe_privilege_drop_imp

/-! ## Functional/imperative equivalence -/

theorem functional_eq_imperative_thm (current_uid : Int) (init_done : Bool) :
    unsafe_privilege_drop current_uid init_done =
      unsafe_privilege_drop_imp current_uid init_done := by
  rfl

theorem implementations_eq_thm :
    unsafe_privilege_drop = unsafe_privilege_drop_imp := by
  funext current_uid init_done
  exact functional_eq_imperative_thm current_uid init_done

end UnsafePrivilegeDrop
end Agent
