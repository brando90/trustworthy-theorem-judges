import Mathlib

/-!
# Natural-number powers with checked integer inputs

Translation of the Python `pre` and `prog` functions. The typed interface uses
`Int` for Python integer arguments; non-integer arguments are excluded by this
type. Negative integers are still representable and produce an explicit
`ValueError`, including the original error message. Successful results are
unbounded integers, computed by repeated multiplication.

The file proves the power specification, nonnegativity, the zero cases, the
successor equation, rejection of invalid inputs, and equivalence with a mutable
`Id.run` loop. Bounded property tests cover every property and the postcondition.
-/

namespace MyPower

/- Functional implementation. -/

inductive PowerError where
  | valueError (message : String)
  deriving DecidableEq, Repr

deriving instance DecidableEq for Except

def valueError (base exponent : Int) : PowerError :=
  .valueError s!"Require base,exponent ∈ ℕ (got base={base}, exponent={exponent})"

def power (base : Nat) : Nat → Nat
  | 0 => 1
  | exponent + 1 => power base exponent * base

def prog (base exponent : Int) : Except PowerError Int :=
  if 0 ≤ base ∧ 0 ≤ exponent then
    .ok (power base.toNat exponent.toNat : Int)
  else
    .error (valueError base exponent)

/- Unit tests, including both Python precondition violations. -/

example : prog 2 3 = .ok 8 := by native_decide
example : prog 0 0 = .ok 1 := by native_decide
example : prog 7 0 = .ok 1 := by native_decide
example : prog 0 7 = .ok 0 := by native_decide
example : prog 1 20 = .ok 1 := by native_decide
example : prog 2 10 = .ok 1024 := by native_decide
example : prog (-1) 2 = .error (.valueError
    "Require base,exponent ∈ ℕ (got base=-1, exponent=2)") := by native_decide
example : prog 2 (-1) = .error (.valueError
    "Require base,exponent ∈ ℕ (got base=2, exponent=-1)") := by native_decide
example : prog (-1) 0 = .error (valueError (-1) 0) := by native_decide

#eval prog 2 3
#eval prog 0 0
#eval prog (-1) 2
#eval prog 2 (-1)

/- Preconditions and proved properties. -/

def Pre (base exponent : Int) : Prop :=
  0 ≤ base ∧ 0 ≤ exponent

theorem power_eq_pow (base exponent : Nat) :
    power base exponent = base ^ exponent := by
  induction exponent with
  | zero => simp [power]
  | succ exponent ih => simp [power, ih, pow_succ]

def power_prop (base exponent : Int) : Prop :=
  prog base exponent = .ok (base ^ exponent.toNat)

theorem power_thm (base exponent : Int) (h : Pre base exponent) :
    power_prop base exponent := by
  rcases h with ⟨hb, he⟩
  simp [power_prop, prog, hb, he, power_eq_pow, Int.toNat_of_nonneg hb]

def nonnegative_prop (base exponent : Int) : Prop :=
  ∃ result : Int, prog base exponent = .ok result ∧ 0 ≤ result

theorem nonnegative_thm (base exponent : Int) (h : Pre base exponent) :
    nonnegative_prop base exponent := by
  exact ⟨base ^ exponent.toNat, power_thm base exponent h, pow_nonneg h.1 _⟩

def zero_exponent_prop (base exponent : Int) : Prop :=
  exponent = 0 → prog base exponent = .ok 1

theorem zero_exponent_thm (base exponent : Int) (h : Pre base exponent) :
    zero_exponent_prop base exponent := by
  intro he
  have hp := power_thm base exponent h
  simpa [power_prop, he] using hp

def zero_base_prop (base exponent : Int) : Prop :=
  base = 0 → 0 < exponent → prog base exponent = .ok 0

theorem zero_base_thm (base exponent : Int) :
    zero_base_prop base exponent := by
  intro hb he
  subst base
  have hp := power_thm 0 exponent ⟨by omega, by omega⟩
  have hn : exponent.toNat ≠ 0 := by omega
  simpa [power_prop, zero_pow hn] using hp

def zero_zero_prop (base exponent : Int) : Prop :=
  base = 0 → exponent = 0 → prog base exponent = .ok 1

theorem zero_zero_thm (base exponent : Int) :
    zero_zero_prop base exponent := by
  intro hb he
  subst base
  subst exponent
  simp [prog, power]

def successor_prop (base exponent : Int) : Prop :=
  prog base (exponent + 1) = (prog base exponent).map (fun result => result * base)

theorem successor_thm (base exponent : Int) (h : Pre base exponent) :
    successor_prop base exponent := by
  have hnext : Pre base (exponent + 1) := ⟨h.1, by have := h.2; omega⟩
  have hp : prog base exponent = .ok (base ^ exponent.toNat) :=
    power_thm base exponent h
  have hpnext : prog base (exponent + 1) = .ok (base ^ (exponent + 1).toNat) :=
    power_thm base (exponent + 1) hnext
  unfold successor_prop
  rw [hpnext, hp]
  simp [Int.toNat_add h.2 (show (0 : Int) ≤ 1 by omega), pow_succ, Except.map]

def invalid_input_prop (base exponent : Int) : Prop :=
  ¬ Pre base exponent → prog base exponent = .error (valueError base exponent)

theorem invalid_input_thm (base exponent : Int) :
    invalid_input_prop base exponent := by
  intro h
  have hinvalid : ¬ (0 ≤ base ∧ 0 ≤ exponent) := h
  simp only [prog, if_neg hinvalid]

/- The postcondition collects the result specification and behavioral laws. -/

def Post_prop (base exponent : Int) : Prop :=
  power_prop base exponent ∧
  nonnegative_prop base exponent ∧
  zero_exponent_prop base exponent ∧
  zero_base_prop base exponent ∧
  zero_zero_prop base exponent ∧
  successor_prop base exponent ∧
  invalid_input_prop base exponent

/- Property-based tests.

Every bounded test visits all 400 pairs in [-4, 15] × [-4, 15]. Properties
whose theorems assume `Pre` are checked on all 256 admissible pairs; the error
property also checks the 144 invalid pairs. The implications in the zero-case
tests retain their original hypotheses. Universal theorems are proved separately.
-/

private def testInputs : List Int :=
  (List.range 20).map (fun n => (n : Int) - 4)

private def checkAll (test : Int → Int → Bool) : Bool :=
  testInputs.all (fun base => testInputs.all (fun exponent => test base exponent))

private def checkAdmissible (test : Int → Int → Bool) : Bool :=
  checkAll (fun base exponent =>
    if 0 ≤ base ∧ 0 ≤ exponent then test base exponent else true)

private def nonnegativeResult : Except PowerError Int → Bool
  | .ok result => decide (0 ≤ result)
  | .error _ => false

-- PBT for power_prop: the implementation agrees with mathematical powers.
example : checkAdmissible (fun base exponent =>
    decide (prog base exponent = .ok (base ^ exponent.toNat))) = true := by
  native_decide

-- Also sample natural inputs, bounding the exponent to keep the run inexpensive.
#eval Plausible.Testable.check (∀ base exponent : Nat,
  prog (base : Int) ((exponent % 20 : Nat) : Int) =
    .ok ((base : Int) ^ (exponent % 20)))

-- PBT for nonnegative_prop: inspect the returned value as its witness.
example : checkAdmissible (fun base exponent =>
    nonnegativeResult (prog base exponent)) = true := by
  native_decide

-- PBT for zero_exponent_prop.
example : checkAdmissible (fun base exponent =>
    decide (exponent = 0 → prog base exponent = .ok 1)) = true := by
  native_decide

-- PBT for zero_base_prop (valid for every integer input pair).
example : checkAll (fun base exponent =>
    decide (base = 0 → 0 < exponent → prog base exponent = .ok 0)) = true := by
  native_decide

-- PBT for zero_zero_prop (valid for every integer input pair).
example : checkAll (fun base exponent =>
    decide (base = 0 → exponent = 0 → prog base exponent = .ok 1)) = true := by
  native_decide

-- PBT for successor_prop.
example : checkAdmissible (fun base exponent =>
    decide (prog base (exponent + 1) =
      (prog base exponent).map (fun result => result * base))) = true := by
  native_decide

-- PBT for invalid_input_prop: validation precedes the exponent-zero case.
example : checkAll (fun base exponent =>
    decide (¬ (0 ≤ base ∧ 0 ≤ exponent) →
      prog base exponent = .error (valueError base exponent))) = true := by
  native_decide

-- Executable form of every conjunct of Post_prop, in the same order.
private def postCheck (base exponent : Int) : Bool :=
  decide (prog base exponent = .ok (base ^ exponent.toNat)) &&
  nonnegativeResult (prog base exponent) &&
  decide (exponent = 0 → prog base exponent = .ok 1) &&
  decide (base = 0 → 0 < exponent → prog base exponent = .ok 0) &&
  decide (base = 0 → exponent = 0 → prog base exponent = .ok 1) &&
  decide (prog base (exponent + 1) =
    (prog base exponent).map (fun result => result * base)) &&
  decide (¬ (0 ≤ base ∧ 0 ≤ exponent) →
    prog base exponent = .error (valueError base exponent))

-- PBT for Post_prop, under exactly the correctness theorem's precondition.
example : checkAdmissible postCheck = true := by native_decide
#eval checkAdmissible postCheck

/- Correctness: every admissible input satisfies the full postcondition. -/

theorem correctness_thm (base exponent : Int) :
    Pre base exponent → Post_prop base exponent := by
  intro h
  exact ⟨power_thm base exponent h,
    nonnegative_thm base exponent h,
    zero_exponent_thm base exponent h,
    zero_base_thm base exponent,
    zero_zero_thm base exponent,
    successor_thm base exponent h,
    invalid_input_thm base exponent⟩

/- Imperative implementation, with the Python validation and early return. -/

def progImperative (base exponent : Int) : Except PowerError Int := Id.run do
  if ¬ (0 ≤ base ∧ 0 ≤ exponent) then
    return .error (valueError base exponent)
  if exponent = 0 then
    return .ok 1
  let mut result : Int := 1
  for _ in List.range exponent.toNat do
    result := result * base
  return .ok result

/- Imperative tests. -/

example : progImperative 2 3 = .ok 8 := by native_decide
example : progImperative 0 0 = .ok 1 := by native_decide
example : progImperative 7 0 = .ok 1 := by native_decide
example : progImperative 0 7 = .ok 0 := by native_decide
example : progImperative (-1) 2 = .error (valueError (-1) 2) := by native_decide
example : progImperative 2 (-1) = .error (valueError 2 (-1)) := by native_decide
example : progImperative (-1) 0 = .error (valueError (-1) 0) := by native_decide

#eval progImperative 2 3
#eval progImperative 0 0
#eval progImperative (-1) 2

-- Check equivalence on both successful and exceptional executions.
example : checkAll (fun base exponent =>
    decide (prog base exponent = progImperative base exponent)) = true := by
  native_decide

/- Loop invariant and equivalence, without assuming the precondition. -/

private theorem foldl_mul_eq (base initial : Int) (indices : List Nat) :
    indices.foldl (fun result _ => result * base) initial =
      initial * base ^ indices.length := by
  induction indices generalizing initial with
  | nil => simp
  | cons index indices ih =>
    simp only [List.foldl_cons, List.length_cons, ih, pow_succ]
    ring

theorem equivalence_thm (base exponent : Int) :
    prog base exponent = progImperative base exponent := by
  by_cases h : 0 ≤ base ∧ 0 ≤ exponent
  · have hp : prog base exponent = .ok (base ^ exponent.toNat) :=
      power_thm base exponent h
    rw [hp]
    by_cases he : exponent = 0
    · subst exponent
      simp [progImperative, h.1]
    · simp only [progImperative, h, if_false, he]
      simp [foldl_mul_eq]
  · simp only [prog, h, if_false, progImperative, not_false_eq_true, if_true]
    rfl

end MyPower
