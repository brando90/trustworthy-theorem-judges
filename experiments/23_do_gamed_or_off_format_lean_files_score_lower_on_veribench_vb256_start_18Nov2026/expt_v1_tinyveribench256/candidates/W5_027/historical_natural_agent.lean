import Mathlib
namespace Agent

/-!
# Unsafe version rollback

Translation of the Python `unsafe_vs_check` from the secure-file-system example.
The check returns `true` without inspecting either version. In particular, it
accepts a stale version structure rather than protecting against rollback.

`Int` models Python's arbitrary-precision signed integers. No nonnegativity or
freshness assumption is imposed. The specification describes the vulnerability;
it does not assert the freshness guarantee that a secure check would provide.
-/

namespace «114_unsafeVersionRollback»

/-! ## Functional implementation -/

/-- The unsafe check ignores both version numbers. -/
def unsafe_vs_check (_client_ver _server_ver : Int) : Bool :=
  true

/-! ## Unit tests: the three Python assertions, plus signed inputs -/

example : unsafe_vs_check 5 5 = true := by native_decide
example : unsafe_vs_check 5 3 = true := by native_decide
example : unsafe_vs_check 100 1 = true := by native_decide
example : unsafe_vs_check (-1) (-10) = true := by native_decide
example : unsafe_vs_check (-5) 10 = true := by native_decide

#eval unsafe_vs_check 5 5
#eval unsafe_vs_check 5 3
#eval unsafe_vs_check 100 1

/-- Executable counterpart of the Python test harness. -/
def check : IO Unit := do
  if unsafe_vs_check 5 5 != true then
    throw (IO.userError "normal case failed")
  if unsafe_vs_check 5 3 != true then
    throw (IO.userError "vuln: old version accepted")
  if unsafe_vs_check 100 1 != true then
    throw (IO.userError "vuln: ancient version accepted")
  IO.println "All tests passed."

#eval check

/-! ## Precondition -/

/-- The Python function accepts every pair of integers. -/
def Pre (_client_ver _server_ver : Int) : Prop := True

/-! ## Properties and kernel-checked proofs -/

/-- Every version structure is accepted, irrespective of freshness. -/
def always_accepts_prop (client_ver server_ver : Int) : Prop :=
  unsafe_vs_check client_ver server_ver = true

theorem always_accepts_thm (client_ver server_ver : Int) :
    always_accepts_prop client_ver server_ver := by
  rfl

/-- Matching client and server versions are accepted (the normal case). -/
def matching_version_prop (version : Int) : Prop :=
  unsafe_vs_check version version = true

theorem matching_version_thm (version : Int) : matching_version_prop version := by
  rfl

/-- Any older server version is also accepted: the rollback vulnerability. -/
def rollback_accepted_prop (client_ver server_ver : Int) : Prop :=
  server_ver < client_ver → unsafe_vs_check client_ver server_ver = true

theorem rollback_accepted_thm (client_ver server_ver : Int) :
    rollback_accepted_prop client_ver server_ver := by
  intro _h_stale
  rfl

/-- Changing either or both version numbers cannot change the result. -/
def version_independent_prop
    (client_ver server_ver other_client other_server : Int) : Prop :=
  unsafe_vs_check client_ver server_ver = unsafe_vs_check other_client other_server

theorem version_independent_thm
    (client_ver server_ver other_client other_server : Int) :
    version_independent_prop client_ver server_ver other_client other_server := by
  rfl

/-! ## Postcondition -/

/-- Exact acceptance behavior together with the normal and vulnerable cases. -/
def Post_prop (client_ver server_ver : Int) : Prop :=
  always_accepts_prop client_ver server_ver ∧
  matching_version_prop client_ver ∧
  rollback_accepted_prop client_ver server_ver ∧
  (∀ other_client other_server : Int,
    version_independent_prop client_ver server_ver other_client other_server)

/-! ## Property-based tests

These checks use executable equalities and comparisons, not proofs of the
specification. The final randomized test expands the entire postcondition,
including universally sampled alternative version numbers.
-/

-- PBT for always_accepts_prop.
#eval Plausible.Testable.check
  (∀ client_ver server_ver : Int, unsafe_vs_check client_ver server_ver = true)

-- PBT for matching_version_prop.
#eval Plausible.Testable.check
  (∀ version : Int, unsafe_vs_check version version = true)

-- PBT for rollback_accepted_prop. Boolean material implication avoids
-- discarding non-stale samples while checking the same property.
#eval Plausible.Testable.check
  (∀ client_ver server_ver : Int,
    ((!decide (server_ver < client_ver)) || unsafe_vs_check client_ver server_ver) = true)

-- Bounded rollback PBT: clients from -20 through 20, and rollback distances
-- from 1 through 41. Every pair constructed here is stale, not a vacuous case.
example :
    (List.range 41).all (fun c =>
      (List.range 41).all (fun d =>
        let client_ver : Int := (c : Int) - 20
        let server_ver : Int := client_ver - ((d : Int) + 1)
        decide (server_ver < client_ver) && unsafe_vs_check client_ver server_ver))
      = true := by native_decide

-- PBT for version_independent_prop.
#eval Plausible.Testable.check
  (∀ client_ver server_ver other_client other_server : Int,
    unsafe_vs_check client_ver server_ver = unsafe_vs_check other_client other_server)

-- PBT for Post_prop, expanded into executable clauses.
#eval Plausible.Testable.check
  (∀ client_ver server_ver other_client other_server : Int,
    unsafe_vs_check client_ver server_ver = true ∧
    unsafe_vs_check client_ver client_ver = true ∧
    (((!decide (server_ver < client_ver)) || unsafe_vs_check client_ver server_ver) = true) ∧
    unsafe_vs_check client_ver server_ver = unsafe_vs_check other_client other_server)

/-- Small signed-integer domain for exhaustive property tests. -/
private def testVersions : List Int :=
  (List.range 11).map (fun n => (n : Int) - 5)

-- Bounded PBT for the whole Post_prop: all four version numbers independently
-- range over -5 through 5. Each conjunction clause matches its specification.
example :
    testVersions.all (fun client_ver =>
      testVersions.all (fun server_ver =>
        testVersions.all (fun other_client =>
          testVersions.all (fun other_server =>
            unsafe_vs_check client_ver server_ver &&
            unsafe_vs_check client_ver client_ver &&
            ((!decide (server_ver < client_ver)) || unsafe_vs_check client_ver server_ver) &&
            (unsafe_vs_check client_ver server_ver ==
              unsafe_vs_check other_client other_server))))) = true := by
  native_decide

/-! ## Correctness -/

/-- Correctness here means faithfully implementing the unsafe behavior. -/
theorem correctness_thm (client_ver server_ver : Int) :
    Pre client_ver server_ver → Post_prop client_ver server_ver := by
  intro _h_pre
  exact ⟨always_accepts_thm client_ver server_ver,
    matching_version_thm client_ver,
    rollback_accepted_thm client_ver server_ver,
    fun other_client other_server =>
      version_independent_thm client_ver server_ver other_client other_server⟩

/-! ## Imperative implementation -/

/-- Mutable-state implementation: approval is set without inspecting versions. -/
def unsafe_vs_check_imp (_client_ver _server_ver : Int) : Bool := Id.run do
  let mut accepted := false
  accepted := true
  return accepted

/-! ## Imperative tests -/

example : unsafe_vs_check_imp 5 5 = true := by native_decide
example : unsafe_vs_check_imp 5 3 = true := by native_decide
example : unsafe_vs_check_imp 100 1 = true := by native_decide
example : unsafe_vs_check_imp (-1) (-10) = true := by native_decide

#eval unsafe_vs_check_imp 5 5
#eval unsafe_vs_check_imp 5 3
#eval unsafe_vs_check_imp 100 1

/-! ## Functional / imperative equivalence -/

/-- Equivalence holds for every pair of signed integers, without assumptions. -/
theorem functional_imperative_equivalence_thm (client_ver server_ver : Int) :
    unsafe_vs_check client_ver server_ver = unsafe_vs_check_imp client_ver server_ver := by
  rfl

end «114_unsafeVersionRollback»
end Agent
