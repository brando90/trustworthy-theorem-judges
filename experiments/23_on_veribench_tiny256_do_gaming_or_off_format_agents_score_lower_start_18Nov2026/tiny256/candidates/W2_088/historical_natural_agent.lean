import Mathlib
namespace Agent

/-!
# Safe chroot UID isolation check

Translation of the Python `safe_chroot_uid` and its `check` routine. Python's
unbounded integers are represented by `Int`. The result is true exactly when
the two UIDs differ; neither directory string participates in the decision.
In particular, separate chroot directories do not make a shared UID acceptable.
This specifies the program's UID-separation check, not a model of all OS security.

All integers (including negative values and root UID zero) and all strings are
admissible. The specification and functional/imperative equivalence are proved
by kernel-checked reasoning; native evaluation is used only for tests.
-/

namespace UnsafeChrootUIDSafe

/-! ## Functional implementation -/

def safe_chroot_uid (service_uid other_uid : Int)
    (_chroot_dir _other_dir : String) : Bool :=
  decide (service_uid ≠ other_uid)

/-! ## Python unit tests -/

example : safe_chroot_uid 1001 1002 "/jail/svc_a" "/jail/svc_b" = true := by
  native_decide

example : safe_chroot_uid 500 999 "/a" "/b" = true := by
  native_decide

example : safe_chroot_uid 1001 1001 "/jail/svc_a" "/jail/svc_b" = false := by
  native_decide

example : safe_chroot_uid 0 0 "/jail/svc_a" "/jail/svc_b" = false := by
  native_decide

example : safe_chroot_uid 500 500 "/a" "/b" = false := by
  native_decide

-- Additional boundary cases: no positivity or directory-separation requirement.
example : safe_chroot_uid (-1) 0 "" "" = true := by
  native_decide

example : safe_chroot_uid (-7) (-7) "/different" "/directories" = false := by
  native_decide

/-- Executable counterpart of the Python `check()` routine. -/
def check : IO Unit := do
  unless safe_chroot_uid 1001 1002 "/jail/svc_a" "/jail/svc_b" do
    throw (IO.userError "different UIDs rejected")
  unless safe_chroot_uid 500 999 "/a" "/b" do
    throw (IO.userError "distinct UIDs rejected")
  if safe_chroot_uid 1001 1001 "/jail/svc_a" "/jail/svc_b" then
    throw (IO.userError "same UID accepted")
  if safe_chroot_uid 0 0 "/jail/svc_a" "/jail/svc_b" then
    throw (IO.userError "root same UID accepted")
  if safe_chroot_uid 500 500 "/a" "/b" then
    throw (IO.userError "duplicate UID accepted")
  IO.println "All tests passed."

#eval check

/-! ## Preconditions and semantic properties -/

/-- The Python function has no restrictions on its typed inputs. -/
def Pre (_service_uid _other_uid : Int) (_chroot_dir _other_dir : String) : Prop :=
  True

/-- Acceptance is equivalent to UID separation, in both directions. -/
def uid_separation_prop (service_uid other_uid : Int)
    (chroot_dir other_dir : String) : Prop :=
  safe_chroot_uid service_uid other_uid chroot_dir other_dir = true ↔
    service_uid ≠ other_uid

theorem uid_separation_thm (service_uid other_uid : Int)
    (chroot_dir other_dir : String) :
    uid_separation_prop service_uid other_uid chroot_dir other_dir := by
  simp [uid_separation_prop, safe_chroot_uid]

/-- Rejection occurs exactly for shared UIDs, including UID zero. -/
def shared_uid_rejection_prop (service_uid other_uid : Int)
    (chroot_dir other_dir : String) : Prop :=
  safe_chroot_uid service_uid other_uid chroot_dir other_dir = false ↔
    service_uid = other_uid

theorem shared_uid_rejection_thm (service_uid other_uid : Int)
    (chroot_dir other_dir : String) :
    shared_uid_rejection_prop service_uid other_uid chroot_dir other_dir := by
  simp [shared_uid_rejection_prop, safe_chroot_uid]

/-- Distinct UIDs are accepted regardless of directory choices. -/
def distinct_uid_acceptance_prop (service_uid other_uid : Int)
    (chroot_dir other_dir : String) : Prop :=
  service_uid ≠ other_uid →
    safe_chroot_uid service_uid other_uid chroot_dir other_dir = true

theorem distinct_uid_acceptance_thm (service_uid other_uid : Int)
    (chroot_dir other_dir : String) :
    distinct_uid_acceptance_prop service_uid other_uid chroot_dir other_dir := by
  intro h
  exact (uid_separation_thm service_uid other_uid chroot_dir other_dir).2 h

/-- Replacing either or both directory strings cannot change the result. -/
def directory_independence_prop (service_uid other_uid : Int)
    (chroot_dir other_dir new_chroot_dir new_other_dir : String) : Prop :=
  safe_chroot_uid service_uid other_uid chroot_dir other_dir =
    safe_chroot_uid service_uid other_uid new_chroot_dir new_other_dir

theorem directory_independence_thm (service_uid other_uid : Int)
    (chroot_dir other_dir new_chroot_dir new_other_dir : String) :
    directory_independence_prop service_uid other_uid
      chroot_dir other_dir new_chroot_dir new_other_dir := by
  rfl

/-- Exchanging the two services does not change the UID-separation check. -/
def symmetry_prop (service_uid other_uid : Int)
    (chroot_dir other_dir : String) : Prop :=
  safe_chroot_uid service_uid other_uid chroot_dir other_dir =
    safe_chroot_uid other_uid service_uid other_dir chroot_dir

theorem symmetry_thm (service_uid other_uid : Int)
    (chroot_dir other_dir : String) :
    symmetry_prop service_uid other_uid chroot_dir other_dir := by
  simp [symmetry_prop, safe_chroot_uid, ne_comm]

/-! ## Postcondition -/

/-- All guarantees, with directory independence quantified over every replacement. -/
def Post_prop (service_uid other_uid : Int)
    (chroot_dir other_dir : String) : Prop :=
  uid_separation_prop service_uid other_uid chroot_dir other_dir ∧
  shared_uid_rejection_prop service_uid other_uid chroot_dir other_dir ∧
  distinct_uid_acceptance_prop service_uid other_uid chroot_dir other_dir ∧
  (∀ new_chroot_dir new_other_dir : String,
    directory_independence_prop service_uid other_uid
      chroot_dir other_dir new_chroot_dir new_other_dir) ∧
  symmetry_prop service_uid other_uid chroot_dir other_dir

/-! ## Property-based tests

The tests below spell out executable checks rather than requiring decidability
instances for the named specification predicates. They are test evidence only;
none is used in any named theorem's proof.
-/

-- PBT for uid_separation_prop.
#eval Plausible.Testable.check
  (∀ service_uid other_uid : Int, ∀ chroot_dir other_dir : String,
    (safe_chroot_uid service_uid other_uid chroot_dir other_dir = true ↔
      service_uid ≠ other_uid))

-- PBT for shared_uid_rejection_prop (checks the exact rejection criterion).
#eval Plausible.Testable.check
  (∀ service_uid other_uid : Int, ∀ chroot_dir other_dir : String,
    (safe_chroot_uid service_uid other_uid chroot_dir other_dir = false ↔
      service_uid = other_uid))

-- PBT for distinct_uid_acceptance_prop. Boolean implication avoids discards:
-- equal UIDs make the hypothesis false; otherwise the result must be true.
#eval Plausible.Testable.check
  (∀ service_uid other_uid : Int, ∀ chroot_dir other_dir : String,
    (decide (service_uid = other_uid) ||
      safe_chroot_uid service_uid other_uid chroot_dir other_dir) = true)

-- PBT for directory_independence_prop, varying all four directory strings.
#eval Plausible.Testable.check
  (∀ service_uid other_uid : Int,
    ∀ chroot_dir other_dir new_chroot_dir new_other_dir : String,
      safe_chroot_uid service_uid other_uid chroot_dir other_dir =
        safe_chroot_uid service_uid other_uid new_chroot_dir new_other_dir)

-- PBT for symmetry_prop.
#eval Plausible.Testable.check
  (∀ service_uid other_uid : Int, ∀ chroot_dir other_dir : String,
    safe_chroot_uid service_uid other_uid chroot_dir other_dir =
      safe_chroot_uid other_uid service_uid other_dir chroot_dir)

-- PBT for Post_prop: all five conjuncts in executable Boolean form.
-- Replacement directories are sampled along with the original inputs.
#eval Plausible.Testable.check
  (∀ service_uid other_uid : Int,
    ∀ chroot_dir other_dir new_chroot_dir new_other_dir : String,
      ((safe_chroot_uid service_uid other_uid chroot_dir other_dir ==
          decide (service_uid ≠ other_uid)) &&
       ((safe_chroot_uid service_uid other_uid chroot_dir other_dir == false) ==
          decide (service_uid = other_uid)) &&
       (decide (service_uid = other_uid) ||
          safe_chroot_uid service_uid other_uid chroot_dir other_dir) &&
       (safe_chroot_uid service_uid other_uid chroot_dir other_dir ==
          safe_chroot_uid service_uid other_uid new_chroot_dir new_other_dir) &&
       (safe_chroot_uid service_uid other_uid chroot_dir other_dir ==
          safe_chroot_uid other_uid service_uid other_dir chroot_dir)) = true)

-- Additional bounded PBT for uid_separation_prop and distinct_uid_acceptance_prop:
-- exhaust equal and unequal UIDs from -15 through 15 and include identical
-- directories, empty strings, and the original test paths.
example :
    (List.range 31).all (fun i =>
      (List.range 31).all (fun j =>
        (["", "/", "/a", "/b", "/jail/svc_a", "/jail/svc_b"] : List String).all
          (fun d =>
            (["", "/", "/a", "/b", "/jail/svc_a", "/jail/svc_b"] : List String).all
              (fun e =>
                let u : Int := (i : Int) - 15
                let v : Int := (j : Int) - 15
                (safe_chroot_uid u v d e == decide (u ≠ v)) &&
                  (decide (u = v) || safe_chroot_uid u v d e))))) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (service_uid other_uid : Int)
    (chroot_dir other_dir : String) :
    Pre service_uid other_uid chroot_dir other_dir →
      Post_prop service_uid other_uid chroot_dir other_dir := by
  intro _hpre
  exact ⟨uid_separation_thm service_uid other_uid chroot_dir other_dir,
    shared_uid_rejection_thm service_uid other_uid chroot_dir other_dir,
    distinct_uid_acceptance_thm service_uid other_uid chroot_dir other_dir,
    (fun new_chroot_dir new_other_dir =>
      directory_independence_thm service_uid other_uid
        chroot_dir other_dir new_chroot_dir new_other_dir),
    symmetry_thm service_uid other_uid chroot_dir other_dir⟩

/-! ## Imperative implementation -/

/-- A mutable flag records whether the two services have distinct UIDs. -/
def safe_chroot_uid_imp (service_uid other_uid : Int)
    (_chroot_dir _other_dir : String) : Bool := Id.run do
  let mut isolated := false
  if service_uid ≠ other_uid then
    isolated := true
  return isolated

/-! ## Imperative unit tests -/

example : safe_chroot_uid_imp 1001 1002 "/jail/svc_a" "/jail/svc_b" = true := by
  native_decide

example : safe_chroot_uid_imp 500 999 "/a" "/b" = true := by
  native_decide

example : safe_chroot_uid_imp 1001 1001 "/jail/svc_a" "/jail/svc_b" = false := by
  native_decide

example : safe_chroot_uid_imp 0 0 "/jail/svc_a" "/jail/svc_b" = false := by
  native_decide

example : safe_chroot_uid_imp 500 500 "/a" "/b" = false := by
  native_decide

#eval [safe_chroot_uid_imp 1001 1002 "/jail/svc_a" "/jail/svc_b",
  safe_chroot_uid_imp 500 999 "/a" "/b",
  safe_chroot_uid_imp 1001 1001 "/jail/svc_a" "/jail/svc_b",
  safe_chroot_uid_imp 0 0 "/jail/svc_a" "/jail/svc_b",
  safe_chroot_uid_imp 500 500 "/a" "/b"]

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equivalence_thm (service_uid other_uid : Int)
    (chroot_dir other_dir : String) :
    safe_chroot_uid service_uid other_uid chroot_dir other_dir =
      safe_chroot_uid_imp service_uid other_uid chroot_dir other_dir := by
  by_cases h : service_uid ≠ other_uid <;>
    simp [safe_chroot_uid, safe_chroot_uid_imp, h]

end UnsafeChrootUIDSafe
end Agent
