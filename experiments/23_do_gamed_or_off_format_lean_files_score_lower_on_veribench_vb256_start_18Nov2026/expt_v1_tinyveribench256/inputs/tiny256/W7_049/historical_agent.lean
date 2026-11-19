import Mathlib
namespace Agent

/-!
# Unsafe SYN handler

A translation of the Python `unsafe_syn_flood` function and its checks.
The handler returns `true` for every SYN, ignoring both the current half-open
count and its configured limit. In particular, an exhausted or overflowing
backlog does not prevent acceptance. This describes the vulnerability rather
than repairing it; the source has no explicit TCB allocation or network state.

Python integers are modeled by `Int`, including negative arguments. There are
no input restrictions. Bounded executable tests provide evidence separately
from the kernel-checked universal proofs.
-/

namespace UnsafeSynFlood

/-! ## Functional implementation -/

def unsafe_syn_flood (_half_open_count _max_half_open : Int) : Bool :=
  true

/-! ## Original unit tests -/

example : unsafe_syn_flood 0 128 = true := by native_decide
example : unsafe_syn_flood 128 128 = true := by native_decide
example : unsafe_syn_flood 999 128 = true := by native_decide
example : unsafe_syn_flood (-1) (-128) = true := by native_decide

def check : IO Unit := do
  unless unsafe_syn_flood 0 128 do
    throw (IO.userError "normal SYN rejected")
  unless unsafe_syn_flood 128 128 do
    throw (IO.userError "vuln: full backlog still accepted")
  unless unsafe_syn_flood 999 128 do
    throw (IO.userError "vuln: overflowed backlog accepted")
  IO.println "All tests passed."

#eval check
#eval (unsafe_syn_flood 0 128, unsafe_syn_flood 128 128,
  unsafe_syn_flood 999 128)

/-! ## Preconditions and semantic properties -/

/-- Every pair of Python integers is admissible. -/
def Pre (_half_open_count _max_half_open : Int) : Prop := True

/-- The handler always accepts, not merely when capacity remains. -/
def alwaysAccepts_prop (half_open_count max_half_open : Int) : Prop :=
  unsafe_syn_flood half_open_count max_half_open = true

theorem alwaysAccepts_thm (half_open_count max_half_open : Int) :
    alwaysAccepts_prop half_open_count max_half_open := by
  rfl

/-- Changing the current connection count has no effect. -/
def countIndependent_prop (half_open_count max_half_open : Int) : Prop :=
  ∀ other_count : Int,
    unsafe_syn_flood half_open_count max_half_open =
      unsafe_syn_flood other_count max_half_open

theorem countIndependent_thm (half_open_count max_half_open : Int) :
    countIndependent_prop half_open_count max_half_open := by
  intro other_count
  rfl

/-- Changing the configured limit has no effect. -/
def limitIndependent_prop (half_open_count max_half_open : Int) : Prop :=
  ∀ other_limit : Int,
    unsafe_syn_flood half_open_count max_half_open =
      unsafe_syn_flood half_open_count other_limit

theorem limitIndependent_thm (half_open_count max_half_open : Int) :
    limitIndependent_prop half_open_count max_half_open := by
  intro other_limit
  rfl

/-- The vulnerability: a full or overflowed backlog is still accepted. -/
def exhaustedBacklog_prop (half_open_count max_half_open : Int) : Prop :=
  max_half_open ≤ half_open_count →
    unsafe_syn_flood half_open_count max_half_open = true

theorem exhaustedBacklog_thm (half_open_count max_half_open : Int) :
    exhaustedBacklog_prop half_open_count max_half_open := by
  intro _hfull
  rfl

/-! ## Postcondition -/

def Post_prop (half_open_count max_half_open : Int) : Prop :=
  alwaysAccepts_prop half_open_count max_half_open ∧
  countIndependent_prop half_open_count max_half_open ∧
  limitIndependent_prop half_open_count max_half_open ∧
  exhaustedBacklog_prop half_open_count max_half_open

/-! ## Property-based tests

Each test checks the executable Boolean counterpart of the named property.
The samples cover every integer from -32 through 32, plus larger signed
values and the original backlog boundary. Universal quantifiers in the
independence properties are sampled over the same finite set. These tests
do not restrict the domains of any theorem.
-/

def pbtInputs : List Int :=
  (List.range 65).map (fun n => (n : Int) - 32) ++
    [-999, -129, -128, 127, 128, 129, 999]

-- PBT for alwaysAccepts_prop.
example :
    (pbtInputs.all fun count =>
      pbtInputs.all fun limit =>
        unsafe_syn_flood count limit) = true := by
  native_decide

-- PBT for countIndependent_prop.
example :
    (pbtInputs.all fun count =>
      pbtInputs.all fun limit =>
        pbtInputs.all fun other_count =>
          unsafe_syn_flood count limit ==
            unsafe_syn_flood other_count limit) = true := by
  native_decide

-- PBT for limitIndependent_prop.
example :
    (pbtInputs.all fun count =>
      pbtInputs.all fun limit =>
        pbtInputs.all fun other_limit =>
          unsafe_syn_flood count limit ==
            unsafe_syn_flood count other_limit) = true := by
  native_decide

-- PBT for exhaustedBacklog_prop, using executable implication.
example :
    (pbtInputs.all fun count =>
      pbtInputs.all fun limit =>
        if limit ≤ count then unsafe_syn_flood count limit else true) = true := by
  native_decide

-- PBT for the complete Post_prop conjunction.
example :
    (pbtInputs.all fun count =>
      pbtInputs.all fun limit =>
        unsafe_syn_flood count limit &&
        (pbtInputs.all fun other_count =>
          unsafe_syn_flood count limit ==
            unsafe_syn_flood other_count limit) &&
        (pbtInputs.all fun other_limit =>
          unsafe_syn_flood count limit ==
            unsafe_syn_flood count other_limit) &&
        (if limit ≤ count then unsafe_syn_flood count limit else true)) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (half_open_count max_half_open : Int) :
    Pre half_open_count max_half_open →
      Post_prop half_open_count max_half_open := by
  intro _hpre
  exact ⟨alwaysAccepts_thm half_open_count max_half_open,
    countIndependent_thm half_open_count max_half_open,
    limitIndependent_thm half_open_count max_half_open,
    exhaustedBacklog_thm half_open_count max_half_open⟩

/-! ## Imperative implementation

A mutable result flag is set unconditionally. Just as in the source, neither
input is inspected and no backlog guard is introduced.
-/

def unsafe_syn_flood_imperative
    (_half_open_count _max_half_open : Int) : Bool := Id.run do
  let mut accepted := false
  accepted := true
  return accepted

/-! ## Imperative tests -/

example : unsafe_syn_flood_imperative 0 128 = true := by native_decide
example : unsafe_syn_flood_imperative 128 128 = true := by native_decide
example : unsafe_syn_flood_imperative 999 128 = true := by native_decide
example : unsafe_syn_flood_imperative (-1) (-128) = true := by native_decide

#eval (unsafe_syn_flood_imperative 0 128,
  unsafe_syn_flood_imperative 128 128,
  unsafe_syn_flood_imperative 999 128)

example :
    (pbtInputs.all fun count =>
      pbtInputs.all fun limit =>
        unsafe_syn_flood count limit ==
          unsafe_syn_flood_imperative count limit) = true := by
  native_decide

/-! ## Functional / imperative equivalence -/

theorem equivalence_thm (half_open_count max_half_open : Int) :
    unsafe_syn_flood half_open_count max_half_open =
      unsafe_syn_flood_imperative half_open_count max_half_open := by
  rfl

end UnsafeSynFlood
end Agent
