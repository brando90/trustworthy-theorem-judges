import Mathlib
namespace Agent

/-!
# Unsafe MAC coverage

Translation of the Python `unsafe_mac_coverage` example from MIT 6.858,
Lecture 14 (TLS). The function returns `true` for either coverage flag.
In particular, lack of MAC coverage for padding is accepted rather than
rejected. This models the unsafe acceptance decision, not the cryptographic
steps of a CBC padding-oracle attack.

The input domain is all Booleans. Property-based tests exhaust both possible
inputs (and all four pairs when comparing inputs). Named theorems are proved
by kernel-checked reduction; `native_decide` is used only in executable tests.
-/

namespace UnsafeMACCoverage

/-- The Python function deliberately ignores whether the MAC covers padding. -/
def unsafe_mac_coverage (_mac_covers_padding : Bool) : Bool :=
  true

-- Unit tests corresponding to the two Python assertions.
example : unsafe_mac_coverage true = true := by native_decide
example : unsafe_mac_coverage false = true := by native_decide

#eval unsafe_mac_coverage true
#eval unsafe_mac_coverage false

/-- Executable counterpart of Python's `check` routine. -/
def check : IO Unit := do
  unless unsafe_mac_coverage true == true do
    throw (IO.userError "MAC-over-padding accepted")
  unless unsafe_mac_coverage false == true do
    throw (IO.userError "vuln: MAC-NOT-over-padding accepted")
  IO.println "All tests passed."

#eval check

/-- Neither value of the coverage flag is excluded. -/
def Pre (_mac_covers_padding : Bool) : Prop := True

/-- The result is always the Boolean `true`. -/
def always_accepts_prop (mac_covers_padding : Bool) : Prop :=
  unsafe_mac_coverage mac_covers_padding = true

theorem always_accepts_thm (mac_covers_padding : Bool) :
    always_accepts_prop mac_covers_padding := by
  rfl

/-- Changing the coverage flag never changes the result. -/
def coverage_independent_prop (mac_covers_padding : Bool) : Prop :=
  ∀ other : Bool,
    unsafe_mac_coverage mac_covers_padding = unsafe_mac_coverage other

theorem coverage_independent_thm (mac_covers_padding : Bool) :
    coverage_independent_prop mac_covers_padding := by
  intro other
  rfl

/-- The unsafe case is accepted: absence of padding coverage is not rejected. -/
def uncovered_padding_accepted_prop (mac_covers_padding : Bool) : Prop :=
  mac_covers_padding = false → unsafe_mac_coverage mac_covers_padding = true

theorem uncovered_padding_accepted_thm (mac_covers_padding : Bool) :
    uncovered_padding_accepted_prop mac_covers_padding := by
  intro _
  rfl

/-- All behavioral guarantees, including the intentionally unsafe acceptance. -/
def Post_prop (mac_covers_padding : Bool) : Prop :=
  always_accepts_prop mac_covers_padding ∧
  coverage_independent_prop mac_covers_padding ∧
  uncovered_padding_accepted_prop mac_covers_padding

-- Property-based tests: exhaustive enumeration is stronger than random
-- sampling here because the entire admissible input domain has two elements.
def booleanInputs : List Bool := [false, true]

-- PBT for always_accepts_prop, using its executable Boolean form.
example : booleanInputs.all
    (fun covered => unsafe_mac_coverage covered == true) = true := by
  native_decide

-- PBT for coverage_independent_prop: exhaust all four pairs of inputs.
example : booleanInputs.all (fun covered =>
    booleanInputs.all (fun other =>
      unsafe_mac_coverage covered == unsafe_mac_coverage other)) = true := by
  native_decide

-- PBT for uncovered_padding_accepted_prop: p → q becomes (!p) || q.
-- In particular, the false input exercises the non-vacuous unsafe case.
example : booleanInputs.all (fun covered =>
    (covered != false) || (unsafe_mac_coverage covered == true)) = true := by
  native_decide

-- PBT for the complete Post_prop conjunction over every admissible input.
example : booleanInputs.all (fun covered =>
    (unsafe_mac_coverage covered == true) &&
    (booleanInputs.all (fun other =>
      unsafe_mac_coverage covered == unsafe_mac_coverage other)) &&
    ((covered != false) || (unsafe_mac_coverage covered == true))) = true := by
  native_decide

#eval booleanInputs.all (fun covered =>
  (unsafe_mac_coverage covered == true) &&
  (booleanInputs.all (fun other =>
    unsafe_mac_coverage covered == unsafe_mac_coverage other)) &&
  ((covered != false) || (unsafe_mac_coverage covered == true)))

/-- The unrestricted precondition implies the full postcondition. -/
theorem correctness_thm (mac_covers_padding : Bool) :
    Pre mac_covers_padding → Post_prop mac_covers_padding := by
  intro _
  exact ⟨always_accepts_thm mac_covers_padding,
    coverage_independent_thm mac_covers_padding,
    uncovered_padding_accepted_thm mac_covers_padding⟩

/-- Imperative rendition: overwrite mutable state with the unconditional result. -/
def unsafe_mac_coverage_imperative (_mac_covers_padding : Bool) : Bool := Id.run do
  let mut accepted := false
  accepted := true
  return accepted

-- Imperative unit tests, including the vulnerable false-input case.
example : unsafe_mac_coverage_imperative true = true := by native_decide
example : unsafe_mac_coverage_imperative false = true := by native_decide

#eval unsafe_mac_coverage_imperative true
#eval unsafe_mac_coverage_imperative false

-- Exhaustive executable comparison of the two implementations.
example : booleanInputs.all (fun covered =>
    unsafe_mac_coverage covered == unsafe_mac_coverage_imperative covered) = true := by
  native_decide

/-- Functional and imperative versions agree for every coverage flag. -/
theorem functional_imperative_equivalence_thm (mac_covers_padding : Bool) :
    unsafe_mac_coverage mac_covers_padding =
      unsafe_mac_coverage_imperative mac_covers_padding := by
  rfl

end UnsafeMACCoverage
end Agent
