import Mathlib
namespace Agent

/-!
# Unsafe firmware updates: no rollback protection

Translation of the Python `unsafe_update_accept` program. Firmware versions are
modeled by `Int`, preserving Python's unbounded signed-integer domain. The updater
always accepts: newer firmware, identical firmware, and older firmware all return
`true`. In particular, every current version has an accepted strictly older
version. This is a vulnerability specification, not an anti-rollback guarantee.

`check` records the five Python assertions as an executable Boolean conjunction.
The imperative model deliberately ignores the version numbers, just like the
functional model. Bounded property-based tests are evidence only; all named
specification and equivalence theorems have kernel-checked proofs.
-/

namespace UnsafeRollback

-- Functional implementation and the executable Python test harness.
def unsafe_update_accept (_new_version _current_version : Int) : Bool :=
  true

def check (candidate : Int → Int → Bool) : Bool :=
  candidate 5 3 &&
  candidate 100 1 &&
  candidate 1 5 &&
  candidate 0 10 &&
  candidate 3 3

-- Unit tests: all five assertions in the source program.
example : unsafe_update_accept 5 3 = true := by native_decide
example : unsafe_update_accept 100 1 = true := by native_decide
example : unsafe_update_accept 1 5 = true := by native_decide
example : unsafe_update_accept 0 10 = true := by native_decide
example : unsafe_update_accept 3 3 = true := by native_decide
example : check unsafe_update_accept = true := by native_decide

-- Python's int annotations do not impose nonnegativity or machine-word bounds.
example : unsafe_update_accept (-10) (-3) = true := by native_decide
example : unsafe_update_accept (-(2 ^ 100)) (2 ^ 100) = true := by native_decide

#eval unsafe_update_accept 1 5
#eval check unsafe_update_accept
#eval if check unsafe_update_accept then "All tests passed." else "Tests failed."

-- There is no admissibility restriction on either version number.
def Pre (_new_version _current_version : Int) : Prop := True

-- Properties of the actual (unsafe) behavior.
def always_accept_prop (new_version current_version : Int) : Prop :=
  unsafe_update_accept new_version current_version = true

theorem always_accept_thm (new_version current_version : Int) :
    always_accept_prop new_version current_version := by
  rfl

def newer_accept_prop (new_version current_version : Int) : Prop :=
  current_version < new_version →
    unsafe_update_accept new_version current_version = true

theorem newer_accept_thm (new_version current_version : Int) :
    newer_accept_prop new_version current_version := by
  intro _
  rfl

-- Every downgrade, not merely the two fixed downgrade examples, is accepted.
def rollback_accept_prop (new_version current_version : Int) : Prop :=
  new_version < current_version →
    unsafe_update_accept new_version current_version = true

theorem rollback_accept_thm (new_version current_version : Int) :
    rollback_accept_prop new_version current_version := by
  intro _
  rfl

def same_accept_prop (version : Int) : Prop :=
  unsafe_update_accept version version = true

theorem same_accept_thm (version : Int) : same_accept_prop version := by
  rfl

-- With unrestricted integers, a rollback is possible even from version zero
-- or a negative version. No nonnegativity premise is silently introduced.
def rollback_vulnerable_prop (current_version : Int) : Prop :=
  ∃ new_version : Int, new_version < current_version ∧
    unsafe_update_accept new_version current_version = true

theorem rollback_vulnerable_thm (current_version : Int) :
    rollback_vulnerable_prop current_version := by
  refine ⟨current_version - 1, ?_, ?_⟩
  · omega
  · rfl

-- The returned value and all behavioral properties form the post-condition.
def Post_prop (new_version current_version : Int) (accepted : Bool) : Prop :=
  accepted = true ∧
  always_accept_prop new_version current_version ∧
  newer_accept_prop new_version current_version ∧
  rollback_accept_prop new_version current_version ∧
  same_accept_prop current_version ∧
  rollback_vulnerable_prop current_version

-- Property-based tests: exhaustive checks of all pairs in a signed test domain.
-- These cover 43 values and 1849 pairs, including both orderings and equality.
def testVersions : List Int :=
  (List.range 41).map (fun n => (n : Int) - 20) ++ [-100, 100]

-- PBT for always_accept_prop.
example : (testVersions.all (fun new_version =>
    testVersions.all (fun current_version =>
      unsafe_update_accept new_version current_version))) = true := by
  native_decide

-- PBT for newer_accept_prop, using its executable implication.
example : (testVersions.all (fun new_version =>
    testVersions.all (fun current_version =>
      decide (current_version < new_version →
        unsafe_update_accept new_version current_version = true)))) = true := by
  native_decide

-- PBT for rollback_accept_prop, including zero and negative versions.
example : (testVersions.all (fun new_version =>
    testVersions.all (fun current_version =>
      decide (new_version < current_version →
        unsafe_update_accept new_version current_version = true)))) = true := by
  native_decide

-- PBT for same_accept_prop: test every version against itself.
example : (testVersions.all (fun version =>
    unsafe_update_accept version version)) = true := by
  native_decide

-- PBT for rollback_vulnerable_prop. Its unbounded existential need not have a
-- Decidable instance: check the constructive witness current_version - 1.
example : (testVersions.all (fun current_version =>
    decide (current_version - 1 < current_version ∧
      unsafe_update_accept (current_version - 1) current_version = true))) = true := by
  native_decide

-- Executable form of the post-condition over the implementation's result.
-- The first conjunct checks both the returned value and always_accept_prop;
-- the last conjunct supplies a witness for rollback_vulnerable_prop.
def postTest (new_version current_version : Int) : Bool :=
  decide (
    unsafe_update_accept new_version current_version = true ∧
    (current_version < new_version →
      unsafe_update_accept new_version current_version = true) ∧
    (new_version < current_version →
      unsafe_update_accept new_version current_version = true) ∧
    unsafe_update_accept current_version current_version = true ∧
    (current_version - 1 < current_version ∧
      unsafe_update_accept (current_version - 1) current_version = true))

-- PBT for Post_prop, with the implementation supplied as the returned value.
example : (testVersions.all (fun new_version =>
    testVersions.all (fun current_version =>
      postTest new_version current_version))) = true := by
  native_decide

#eval testVersions.all (fun new_version =>
  testVersions.all (fun current_version => postTest new_version current_version))

-- Correctness means faithful acceptance, not protection against rollback.
theorem correctness_thm (new_version current_version : Int) :
    Pre new_version current_version →
    Post_prop new_version current_version
      (unsafe_update_accept new_version current_version) := by
  intro _
  exact ⟨rfl,
    always_accept_thm new_version current_version,
    newer_accept_thm new_version current_version,
    rollback_accept_thm new_version current_version,
    same_accept_thm current_version,
    rollback_vulnerable_thm current_version⟩

-- Imperative implementation with a mutable acceptance flag, and no comparison.
def unsafe_update_accept_imperative
    (_new_version _current_version : Int) : Bool := Id.run do
  let mut accepted := false
  accepted := true
  return accepted

-- Imperative tests mirror the five assertions and check the full harness.
example : unsafe_update_accept_imperative 5 3 = true := by native_decide
example : unsafe_update_accept_imperative 100 1 = true := by native_decide
example : unsafe_update_accept_imperative 1 5 = true := by native_decide
example : unsafe_update_accept_imperative 0 10 = true := by native_decide
example : unsafe_update_accept_imperative 3 3 = true := by native_decide
example : check unsafe_update_accept_imperative = true := by native_decide

#eval check unsafe_update_accept_imperative

-- Bounded agreement test, followed by the universal kernel-checked proof.
example : (testVersions.all (fun new_version =>
    testVersions.all (fun current_version =>
      decide (unsafe_update_accept new_version current_version =
        unsafe_update_accept_imperative new_version current_version)))) = true := by
  native_decide

theorem functional_imperative_equivalence_thm (new_version current_version : Int) :
    unsafe_update_accept new_version current_version =
      unsafe_update_accept_imperative new_version current_version := by
  rfl

end UnsafeRollback
end Agent
