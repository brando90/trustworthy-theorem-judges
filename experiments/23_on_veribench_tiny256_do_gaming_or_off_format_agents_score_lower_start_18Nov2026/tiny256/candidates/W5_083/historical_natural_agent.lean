import Mathlib
namespace Agent

/-!
# Unsafe privilege escalation via setuid

A translation of the Python `unsafe_setuid` example from MIT 6.858
Quiz 1, Spring 2014. The function always returns `true`: it does not
check whether the caller is root (UID 0). In particular, an unprivileged
caller is allowed to request UID 0 or any other target UID.

Python integers are modeled by `Int`, without imposing nonnegativity or
any other restriction absent from the source. The Boolean represents
acceptance of the request; the source does not actually modify an OS UID.
The specifications describe the vulnerability, not a repaired policy.
-/

namespace UnsafePrivilegeEscalation

/-! ## Functional implementation -/

/-- Accept every request, deliberately ignoring both arguments. -/
def unsafe_setuid (_current_uid _target_uid : Int) : Bool :=
  true

/-! ## Original unit tests -/

example : unsafe_setuid 0 1000 = true := by native_decide
example : unsafe_setuid 1001 0 = true := by native_decide
example : unsafe_setuid 1001 1002 = true := by native_decide

/-- Executable counterpart of the Python `check` routine. -/
def check : IO Unit := do
  unless unsafe_setuid 0 1000 do
    throw (IO.userError "root→user rejected")
  unless unsafe_setuid 1001 0 do
    throw (IO.userError "vuln: unprivileged→root accepted")
  unless unsafe_setuid 1001 1002 do
    throw (IO.userError "vuln: unprivileged uid change accepted")
  IO.println "All tests passed."

#eval check
#eval unsafe_setuid 0 1000
#eval unsafe_setuid 1001 0
#eval unsafe_setuid 1001 1002

/-! ## Precondition -/

/-- The Python function accepts every pair of integers. -/
def Pre (_current_uid _target_uid : Int) : Prop := True

/-! ## Behavioral properties and kernel-checked proofs -/

/-- The exact return-value specification on the entire input domain. -/
def always_accepts_prop (current_uid target_uid : Int) : Prop :=
  unsafe_setuid current_uid target_uid = true

theorem always_accepts_thm (current_uid target_uid : Int) :
    always_accepts_prop current_uid target_uid := by
  rfl

/-- A root caller can request any target UID. -/
def root_to_user_prop (target_uid : Int) : Prop :=
  unsafe_setuid 0 target_uid = true

theorem root_to_user_thm (target_uid : Int) :
    root_to_user_prop target_uid := by
  rfl

/-- The vulnerability: every non-root caller is accepted when requesting root. -/
def unprivileged_to_root_prop (current_uid : Int) : Prop :=
  current_uid ≠ 0 → unsafe_setuid current_uid 0 = true

theorem unprivileged_to_root_thm (current_uid : Int) :
    unprivileged_to_root_prop current_uid := by
  intro _
  rfl

/-- Non-root callers can also request arbitrary other UIDs. -/
def unprivileged_change_prop (current_uid target_uid : Int) : Prop :=
  current_uid ≠ 0 → unsafe_setuid current_uid target_uid = true

theorem unprivileged_change_thm (current_uid target_uid : Int) :
    unprivileged_change_prop current_uid target_uid := by
  intro _
  rfl

/-- Neither the caller UID nor the target UID affects the result. -/
def input_independence_prop
    (current_uid target_uid other_current_uid other_target_uid : Int) : Prop :=
  unsafe_setuid current_uid target_uid =
    unsafe_setuid other_current_uid other_target_uid

theorem input_independence_thm
    (current_uid target_uid other_current_uid other_target_uid : Int) :
    input_independence_prop current_uid target_uid
      other_current_uid other_target_uid := by
  rfl

/-! ## Postcondition -/

/-- All behavioral guarantees, including the unsafe acceptance cases. -/
def Post_prop (current_uid target_uid : Int) : Prop :=
  always_accepts_prop current_uid target_uid ∧
  root_to_user_prop target_uid ∧
  unprivileged_to_root_prop current_uid ∧
  unprivileged_change_prop current_uid target_uid ∧
  (∀ other_current_uid other_target_uid : Int,
    input_independence_prop current_uid target_uid
      other_current_uid other_target_uid)

/-! ## Property-based tests

These checks exercise executable forms of each property. They are testing
evidence only; none is used in a theorem proof. The postcondition test
also samples the universally quantified comparison UIDs.
-/

-- PBT: always_accepts_prop.
#eval Plausible.Testable.check
  (∀ current_uid target_uid : Int,
    unsafe_setuid current_uid target_uid = true)

-- PBT: root_to_user_prop.
#eval Plausible.Testable.check
  (∀ target_uid : Int, unsafe_setuid 0 target_uid = true)

-- PBT: unprivileged_to_root_prop.
#eval Plausible.Testable.check
  (∀ current_uid : Int,
    decide (current_uid ≠ 0 → unsafe_setuid current_uid 0 = true) = true)

-- PBT: unprivileged_change_prop.
#eval Plausible.Testable.check
  (∀ current_uid target_uid : Int,
    decide (current_uid ≠ 0 → unsafe_setuid current_uid target_uid = true) = true)

-- PBT: input_independence_prop.
#eval Plausible.Testable.check
  (∀ current_uid target_uid other_current_uid other_target_uid : Int,
    unsafe_setuid current_uid target_uid =
      unsafe_setuid other_current_uid other_target_uid)

-- PBT: Post_prop, with its conjunction expanded to executable checks.
-- Deciding implications as Booleans avoids discarding root samples.
#eval Plausible.Testable.check
  (∀ current_uid target_uid other_current_uid other_target_uid : Int,
    decide (
      unsafe_setuid current_uid target_uid = true ∧
      unsafe_setuid 0 target_uid = true ∧
      (current_uid ≠ 0 → unsafe_setuid current_uid 0 = true) ∧
      (current_uid ≠ 0 → unsafe_setuid current_uid target_uid = true) ∧
      unsafe_setuid current_uid target_uid =
        unsafe_setuid other_current_uid other_target_uid) = true)

/-- A bounded sample containing negative UIDs, root, and the original test UIDs. -/
def pbtUIDs : List Int :=
  (List.range 25).map (fun n => (n : Int) - 12) ++ [1000, 1001, 1002]

-- Bounded PBT: unprivileged_to_root_prop; all non-root samples are checked.
example : pbtUIDs.all (fun current_uid =>
    decide (current_uid ≠ 0 → unsafe_setuid current_uid 0 = true)) = true := by
  native_decide

-- Bounded PBT: unprivileged_change_prop, exhaustively over sample pairs.
example : pbtUIDs.all (fun current_uid =>
    pbtUIDs.all (fun target_uid =>
      decide (current_uid ≠ 0 → unsafe_setuid current_uid target_uid = true)))
    = true := by
  native_decide

-- Bounded PBT: Post_prop; comparison UIDs are also exhaustively sampled.
example : pbtUIDs.all (fun current_uid =>
    pbtUIDs.all (fun target_uid =>
      pbtUIDs.all (fun other_current_uid =>
        pbtUIDs.all (fun other_target_uid =>
          decide (
            unsafe_setuid current_uid target_uid = true ∧
            unsafe_setuid 0 target_uid = true ∧
            (current_uid ≠ 0 → unsafe_setuid current_uid 0 = true) ∧
            (current_uid ≠ 0 → unsafe_setuid current_uid target_uid = true) ∧
            unsafe_setuid current_uid target_uid =
              unsafe_setuid other_current_uid other_target_uid))))) = true := by
  native_decide

/-! ## Correctness -/

/-- The implementation satisfies the unsafe specification on every input. -/
theorem correctness_thm (current_uid target_uid : Int) :
    Pre current_uid target_uid → Post_prop current_uid target_uid := by
  intro _
  exact ⟨always_accepts_thm current_uid target_uid,
    root_to_user_thm target_uid,
    unprivileged_to_root_thm current_uid,
    unprivileged_change_thm current_uid target_uid,
    fun other_current_uid other_target_uid =>
      input_independence_thm current_uid target_uid
        other_current_uid other_target_uid⟩

/-! ## Imperative implementation -/

/-- An equivalent local mutable-state computation, with no authorization check. -/
def unsafe_setuid_imperative (_current_uid _target_uid : Int) : Bool :=
  Id.run do
    let mut accepted := false
    accepted := true
    return accepted

/-! ## Imperative tests -/

example : unsafe_setuid_imperative 0 1000 = true := by native_decide
example : unsafe_setuid_imperative 1001 0 = true := by native_decide
example : unsafe_setuid_imperative 1001 1002 = true := by native_decide

#eval unsafe_setuid_imperative 0 1000
#eval unsafe_setuid_imperative 1001 0
#eval unsafe_setuid_imperative 1001 1002

-- PBT: pointwise functional/imperative equivalence.
#eval Plausible.Testable.check
  (∀ current_uid target_uid : Int,
    unsafe_setuid current_uid target_uid =
      unsafe_setuid_imperative current_uid target_uid)

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equivalence_thm (current_uid target_uid : Int) :
    unsafe_setuid current_uid target_uid =
      unsafe_setuid_imperative current_uid target_uid := by
  rfl

end UnsafePrivilegeEscalation
end Agent
