import Mathlib
namespace Agent

/-!
# Unsafe version installation

Translation of the Python `unsafe_version_install` program. Python integers are
modelled by `Int`, with no restriction to nonnegative versions. The installer
returns `true` without inspecting either version. In particular, it accepts any
older version: this models the version-downgrade vulnerability, not a repaired
installer. Signature verification is not an operation of the source function.

The five source assertions appear below as unit tests. Universal acceptance,
upgrade/same-version/downgrade acceptance, and independence from both arguments
are proved separately. Bounded property-based tests exercise signed inputs;
they are test evidence only and are not used in any theorem proof.
-/

namespace UnsafeVersionDowngrade

/-! ## Functional implementation -/

/-- The source program unconditionally accepts the requested installation. -/
def unsafe_version_install (_current_ver _install_ver : Int) : Bool :=
  true

/-! ## Unit tests (the five Python assertions) -/

example : unsafe_version_install 10 11 = true := by native_decide
example : unsafe_version_install 10 10 = true := by native_decide
example : unsafe_version_install 10 9 = true := by native_decide
example : unsafe_version_install 100 1 = true := by native_decide
example : unsafe_version_install 0 0 = true := by native_decide

#eval unsafe_version_install 10 11
#eval unsafe_version_install 10 10
#eval unsafe_version_install 10 9
#eval unsafe_version_install 100 1
#eval unsafe_version_install 0 0

/-- The Python `check` routine, including its assertion messages. -/
def check : IO Unit := do
  unless unsafe_version_install 10 11 == true do
    throw (IO.userError "upgrade case")
  unless unsafe_version_install 10 10 == true do
    throw (IO.userError "same version")
  unless unsafe_version_install 10 9 == true do
    throw (IO.userError "vuln: downgrade accepted")
  unless unsafe_version_install 100 1 == true do
    throw (IO.userError "vuln: major downgrade")
  unless unsafe_version_install 0 0 == true do
    throw (IO.userError "zero versions")
  IO.println "All tests passed."

#eval check

/-! ## Precondition and properties -/

/-- Every pair of Python integers is admissible. -/
def Pre (_current_ver _install_ver : Int) : Prop := True

/-- The exact return value for all inputs. -/
def always_accepts_prop (current_ver install_ver : Int) : Prop :=
  unsafe_version_install current_ver install_ver = true

theorem always_accepts_thm (current_ver install_ver : Int) :
    always_accepts_prop current_ver install_ver := by
  rfl

/-- Installing a newer image succeeds. -/
def upgrade_accepted_prop (current_ver install_ver : Int) : Prop :=
  current_ver < install_ver → unsafe_version_install current_ver install_ver = true

theorem upgrade_accepted_thm (current_ver install_ver : Int) :
    upgrade_accepted_prop current_ver install_ver := by
  intro _
  rfl

/-- Installing the current version also succeeds. -/
def same_version_accepted_prop (current_ver : Int) : Prop :=
  unsafe_version_install current_ver current_ver = true

theorem same_version_accepted_thm (current_ver : Int) :
    same_version_accepted_prop current_ver := by
  rfl

/-- The vulnerability: every strictly older version is accepted. -/
def downgrade_accepted_prop (current_ver install_ver : Int) : Prop :=
  install_ver < current_ver → unsafe_version_install current_ver install_ver = true

theorem downgrade_accepted_thm (current_ver install_ver : Int) :
    downgrade_accepted_prop current_ver install_ver := by
  intro _
  rfl

/-- Changing either or both version arguments cannot change the result. -/
def input_independence_prop
    (current_ver install_ver other_current other_install : Int) : Prop :=
  unsafe_version_install current_ver install_ver =
    unsafe_version_install other_current other_install

theorem input_independence_thm
    (current_ver install_ver other_current other_install : Int) :
    input_independence_prop current_ver install_ver other_current other_install := by
  rfl

/-! ## Postcondition -/

/-- Per-call behavior, including all three version-ordering cases.
The four-input relational property is proved separately above. -/
def Post_prop (current_ver install_ver : Int) : Prop :=
  always_accepts_prop current_ver install_ver ∧
  upgrade_accepted_prop current_ver install_ver ∧
  same_version_accepted_prop current_ver ∧
  downgrade_accepted_prop current_ver install_ver

/-! ## Property-based tests

These checks use executable forms of each specification, rather than relying on
a `Decidable` instance for a specification definition. The bounded domain contains
negative, zero, and positive integers and exercises all three ordering cases.
-/

/-- All integers from -20 through 20, inclusive. -/
def testVersions : List Int :=
  (List.range 41).map (fun n => (n : Int) - 20)

-- PBT for always_accepts_prop: exhaustive pairs of signed versions.
example : testVersions.all (fun current_ver =>
    testVersions.all (fun install_ver =>
      unsafe_version_install current_ver install_ver)) = true := by
  native_decide

-- PBT for upgrade_accepted_prop: executable decidable implication.
example : testVersions.all (fun current_ver =>
    testVersions.all (fun install_ver =>
      decide (current_ver < install_ver →
        unsafe_version_install current_ver install_ver = true))) = true := by
  native_decide

-- PBT for same_version_accepted_prop.
example : testVersions.all (fun current_ver =>
    unsafe_version_install current_ver current_ver) = true := by
  native_decide

-- PBT for downgrade_accepted_prop, including strictly negative versions.
example : testVersions.all (fun current_ver =>
    testVersions.all (fun install_ver =>
      decide (install_ver < current_ver →
        unsafe_version_install current_ver install_ver = true))) = true := by
  native_decide

-- PBT for input_independence_prop: all quadruples from -3 through 3.
example :
    let versions := (List.range 7).map (fun n => (n : Int) - 3)
    versions.all (fun current_ver =>
      versions.all (fun install_ver =>
        versions.all (fun other_current =>
          versions.all (fun other_install =>
            unsafe_version_install current_ver install_ver ==
              unsafe_version_install other_current other_install)))) = true := by
  native_decide

-- PBT for the full Post_prop: conjunction of its executable components.
example : testVersions.all (fun current_ver =>
    testVersions.all (fun install_ver =>
      decide (
        unsafe_version_install current_ver install_ver = true ∧
        (current_ver < install_ver →
          unsafe_version_install current_ver install_ver = true) ∧
        unsafe_version_install current_ver current_ver = true ∧
        (install_ver < current_ver →
          unsafe_version_install current_ver install_ver = true)))) = true := by
  native_decide

/-! ## Correctness -/

/-- Correctness means faithfully reproducing the unsafe program, not enforcing
an anti-downgrade security policy. -/
theorem correctness_thm (current_ver install_ver : Int) :
    Pre current_ver install_ver → Post_prop current_ver install_ver := by
  intro _
  exact ⟨always_accepts_thm current_ver install_ver,
    upgrade_accepted_thm current_ver install_ver,
    same_version_accepted_thm current_ver,
    downgrade_accepted_thm current_ver install_ver⟩

/-! ## Imperative implementation -/

/-- A mutable result is assigned unconditionally, with no version comparison. -/
def unsafe_version_install_imperative (_current_ver _install_ver : Int) : Bool :=
  Id.run do
    let mut accepted := false
    accepted := true
    return accepted

/-! ## Imperative tests -/

example : unsafe_version_install_imperative 10 11 = true := by native_decide
example : unsafe_version_install_imperative 10 10 = true := by native_decide
example : unsafe_version_install_imperative 10 9 = true := by native_decide
example : unsafe_version_install_imperative 100 1 = true := by native_decide
example : unsafe_version_install_imperative 0 0 = true := by native_decide

#eval unsafe_version_install_imperative 10 11
#eval unsafe_version_install_imperative 10 10
#eval unsafe_version_install_imperative 10 9
#eval unsafe_version_install_imperative 100 1
#eval unsafe_version_install_imperative 0 0

-- Bounded functional/imperative comparison over signed inputs.
example : testVersions.all (fun current_ver =>
    testVersions.all (fun install_ver =>
      unsafe_version_install current_ver install_ver ==
        unsafe_version_install_imperative current_ver install_ver)) = true := by
  native_decide

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equivalence_thm (current_ver install_ver : Int) :
    unsafe_version_install current_ver install_ver =
      unsafe_version_install_imperative current_ver install_ver := by
  rfl

end UnsafeVersionDowngrade
end Agent
