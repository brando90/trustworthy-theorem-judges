import Mathlib
namespace Agent

/-!
# Sum of decimal digits

A translation of the Python `pre` and `prog`. The mathematical core uses `Nat`,
so integers are unbounded. The checked interface retains negative integers and
non-integer inputs and returns `Except.error .valueError` on a precondition
violation. Python Booleans count as integers (False = 0, True = 1). `other`
represents all other non-integer Python objects; their contents are irrelevant.
A floating-point payload is inspected only for its type, never rounded to an
integer. Exception text is abstracted, but the exception class is preserved.

The independent specification is the sum of Mathlib's base-ten digit list.
The imperative loop below uses a well-founded recursive back-edge, rather than
an unsafe/partial while loop: each iteration mutates the same two mathematical
state components as Python, and division by ten strictly decreases the remainder.
-/

namespace MySumDigits

/-! ## Functional implementation and input validation -/

def sumDigits (n : Nat) : Nat :=
  if h : n = 0 then 0 else n % 10 + sumDigits (n / 10)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

inductive Input where
  | integer (value : Int)
  | boolean (value : Bool)
  | floating (value : Float)
  | other (description : String)

inductive Error where
  | valueError
  deriving DecidableEq, Repr

-- Except does not supply executable equality by default in this Lean version.
deriving instance DecidableEq for Except

/-- Perform the Python integer-type and nonnegativity checks. -/
def asNat : Input → Option Nat
  | .integer z => if 0 ≤ z then some z.toNat else none
  | .boolean b => some (if b then 1 else 0)
  | .floating _ => none
  | .other _ => none

def pre (x : Input) : Bool := (asNat x).isSome

def prog (x : Input) : Except Error Nat :=
  match asNat x with
  | some n => .ok (sumDigits n)
  | none => .error .valueError

/-! ## Fixed unit tests -/

example : sumDigits 123 = 6 := by native_decide
example : sumDigits 0 = 0 := by native_decide
example : sumDigits 7 = 7 := by native_decide
example : sumDigits 1002003 = 6 := by native_decide
example : sumDigits 99999 = 45 := by native_decide
example : prog (.integer 123) = .ok 6 := by native_decide
example : prog (.integer 0) = .ok 0 := by native_decide
example : prog (.integer (-1)) = .error .valueError := by native_decide
example : prog (.floating 3.14) = .error .valueError := by native_decide
example : prog (.floating 3.0) = .error .valueError := by native_decide
example : prog (.boolean true) = .ok 1 := by native_decide
example : prog (.boolean false) = .ok 0 := by native_decide
example : prog (.other "123") = .error .valueError := by native_decide
#eval sumDigits 123
#eval prog (.integer 0)
#eval prog (.integer (-1))
#eval prog (.floating 3.14)

/-! ## Precondition -/

/-- Exactly the admissible Python values, including the integer subclass Bool. -/
def Pre (x : Input) : Prop := pre x = true

theorem pre_integer_thm (z : Int) : Pre (.integer z) ↔ 0 ≤ z := by
  simp [Pre, pre, asNat]

theorem pre_boolean_thm (b : Bool) : Pre (.boolean b) := by
  simp [Pre, pre, asNat]

theorem pre_floating_thm (x : Float) : ¬ Pre (.floating x) := by
  simp [Pre, pre, asNat]

theorem pre_other_thm (s : String) : ¬ Pre (.other s) := by
  simp [Pre, pre, asNat]

/-! ## Mathematical properties, with kernel-checked proofs -/

def zero_prop : Prop := sumDigits 0 = 0

theorem zero_thm : zero_prop := by
  unfold zero_prop
  rw [sumDigits]
  simp

def step_prop (n : Nat) : Prop :=
  0 < n → sumDigits n = n % 10 + sumDigits (n / 10)

theorem step_thm (n : Nat) : step_prop n := by
  intro h
  rw [sumDigits]
  simp [Nat.ne_of_gt h]

def single_digit_prop (n : Nat) : Prop := n < 10 → sumDigits n = n

theorem single_digit_thm (n : Nat) : single_digit_prop n := by
  intro hn
  by_cases h : n = 0
  · subst n
    exact zero_thm
  · rw [step_thm n (Nat.pos_of_ne_zero h), Nat.mod_eq_of_lt hn,
      Nat.div_eq_of_lt hn, zero_thm, Nat.add_zero]

def digits_prop (n : Nat) : Prop := sumDigits n = (Nat.digits 10 n).sum

theorem digits_thm (n : Nat) : digits_prop n := by
  unfold digits_prop
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa using zero_thm
    · rw [step_thm n (Nat.pos_of_ne_zero hn),
        Nat.digits_eq_cons_digits_div (by decide : 1 < 10) hn, List.sum_cons,
        ih (n / 10) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))]

def bound_prop (n : Nat) : Prop := sumDigits n ≤ n

theorem bound_thm (n : Nat) : bound_prop n := by
  unfold bound_prop
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      rw [zero_thm]
    · rw [step_thm n (Nat.pos_of_ne_zero hn)]
      have hi := ih (n / 10) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))
      have hd := Nat.mod_add_div n 10
      omega

def zero_iff_prop (n : Nat) : Prop := sumDigits n = 0 ↔ n = 0

theorem zero_iff_thm (n : Nat) : zero_iff_prop n := by
  unfold zero_iff_prop
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp [show sumDigits 0 = 0 from zero_thm]
    · have hi := ih (n / 10) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))
      rw [step_thm n (Nat.pos_of_ne_zero hn)]
      have hd := Nat.mod_add_div n 10
      omega

def mod_nine_prop (n : Nat) : Prop := sumDigits n % 9 = n % 9

theorem mod_nine_thm (n : Nat) : mod_nine_prop n := by
  unfold mod_nine_prop
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      rw [zero_thm]
    · rw [step_thm n (Nat.pos_of_ne_zero hn), Nat.add_mod,
        ih (n / 10) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))]
      have hd := Nat.mod_add_div n 10
      omega

/-- A successful return occurs exactly on inputs satisfying Python's precondition. -/
def validation_prop (x : Input) : Prop :=
  (prog x).isOk = true ↔ Pre x

theorem validation_thm (x : Input) : validation_prop x := by
  unfold validation_prop prog Pre pre
  cases asNat x <;> rfl

/-- Invalid inputs return ValueError, rather than being silently coerced. -/
def rejection_prop (x : Input) : Prop :=
  ¬ Pre x → prog x = .error .valueError

theorem rejection_thm (x : Input) : rejection_prop x := by
  unfold rejection_prop Pre pre prog
  cases asNat x <;> simp

/-! ## Postcondition -/

/-- Total checked specification: exact digit sum and its mathematical properties
on valid inputs, and ValueError on invalid ones. -/
def Post_prop (x : Input) (result : Except Error Nat) : Prop :=
  validation_prop x ∧ rejection_prop x ∧
  match asNat x with
  | none => result = .error .valueError
  | some n => result = .ok ((Nat.digits 10 n).sum) ∧
      digits_prop n ∧ bound_prop n ∧ zero_iff_prop n ∧
      single_digit_prop n ∧ step_prop n ∧ mod_nine_prop n

/-! ## Property-based tests

Each executable property has an exhaustive bounded check below. The checked
interface is exercised on both sides of the integer boundary, on both Booleans,
on fractional and integral floats, and on a representative other object.
These tests are evidence only; none is used by a theorem.
-/

example : ([0] : List Nat).all (fun n => sumDigits n == 0) = true := by native_decide
example : (List.range 1000).all (fun n =>
    decide (0 < n → sumDigits n = n % 10 + sumDigits (n / 10))) = true := by
  native_decide
example : (List.range 1000).all (fun n =>
    decide (n < 10 → sumDigits n = n)) = true := by native_decide
example : (List.range 1000).all (fun n =>
    sumDigits n == (Nat.digits 10 n).sum) = true := by native_decide
example : (List.range 1000).all (fun n => decide (sumDigits n ≤ n)) = true := by
  native_decide
example : (List.range 1000).all (fun n =>
    decide (sumDigits n = 0 ↔ n = 0)) = true := by native_decide
example : (List.range 1000).all (fun n => sumDigits n % 9 == n % 9) = true := by
  native_decide

def inputSamples : List Input :=
  (List.range 1000).map (fun n => .integer (Int.ofNat n)) ++
  (List.range 100).map (fun n => .integer (- (Int.ofNat n + 1))) ++
  [.boolean false, .boolean true, .floating 3.14, .floating 3.0,
   .floating (-2.5), .other "None", .other "123"]

-- PBT for validation_prop.
example : inputSamples.all (fun x => (prog x).isOk == pre x) = true := by
  native_decide
-- PBT for rejection_prop.
example : inputSamples.all (fun x =>
    decide (pre x = false → prog x = .error .valueError)) = true := by native_decide

/-- Executable expansion of every conjunct in Post_prop. -/
def postCheck (x : Input) (result : Except Error Nat) : Bool :=
  ((prog x).isOk == pre x) &&
  decide (pre x = false → prog x = .error .valueError) &&
  match asNat x with
  | none => decide (result = .error .valueError)
  | some n => decide (result = .ok ((Nat.digits 10 n).sum)) &&
      (sumDigits n == (Nat.digits 10 n).sum) && decide (sumDigits n ≤ n) &&
      decide (sumDigits n = 0 ↔ n = 0) && decide (n < 10 → sumDigits n = n) &&
      decide (0 < n → sumDigits n = n % 10 + sumDigits (n / 10)) &&
      (sumDigits n % 9 == n % 9)

example : inputSamples.all (fun x => postCheck x (prog x)) = true := by native_decide
#eval inputSamples.all (fun x => postCheck x (prog x))
#eval Plausible.Testable.check (∀ n : Nat, sumDigits n = (Nat.digits 10 n).sum)
#eval Plausible.Testable.check (∀ n : Nat, sumDigits n ≤ n)

/-! ## Correctness -/

theorem postCheck_iff_thm (x : Input) (r : Except Error Nat) :
    postCheck x r = true ↔ Post_prop x r := by
  unfold postCheck Post_prop validation_prop rejection_prop Pre
  cases h : asNat x <;>
    simp [pre, prog, h, digits_prop, bound_prop, zero_iff_prop, single_digit_prop,
      step_prop, mod_nine_prop, Bool.and_eq_true, and_assoc, imp_iff_not_or]

/-- The interface is correct even when its precondition is violated. -/
theorem total_correctness_thm (x : Input) : Post_prop x (prog x) := by
  refine ⟨validation_thm x, rejection_thm x, ?_⟩
  cases h : asNat x with
  | none => simp [prog, h]
  | some n =>
    exact ⟨by simpa [prog, h] using congrArg (Except.ok (ε := Error)) (digits_thm n),
      digits_thm n, bound_thm n, zero_iff_thm n, single_digit_thm n,
      step_thm n, mod_nine_thm n⟩

theorem correctness_thm (x : Input) : Pre x → Post_prop x (prog x) := by
  intro _
  exact total_correctness_thm x

/-! ## Imperative implementation

`digitLoop` is the Python while-loop with a total recursive back-edge. No fuel
bound changes its behavior. Both assignments occur before the next iteration,
and the accumulator is never reset. The decreasing remainder proves termination.
-/

def digitLoop (remaining total : Nat) : Nat := Id.run do
  let mut n := remaining
  let mut acc := total
  if h : n = 0 then
    return acc
  else
    acc := acc + n % 10
    n := n / 10
    return digitLoop n acc
termination_by remaining
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

def sumDigitsImperative (n : Nat) : Nat := Id.run do
  let mut total := 0
  total := digitLoop n total
  return total

def progImperative (x : Input) : Except Error Nat := Id.run do
  match asNat x with
  | none => return .error .valueError
  | some n =>
    let mut total := 0
    total := sumDigitsImperative n
    return .ok total

/-! ## Imperative tests -/

example : sumDigitsImperative 123 = 6 := by native_decide
example : sumDigitsImperative 0 = 0 := by native_decide
example : sumDigitsImperative 8 = 8 := by native_decide
example : sumDigitsImperative 1002003 = 6 := by native_decide
example : progImperative (.integer (-1)) = .error .valueError := by native_decide
example : progImperative (.floating 3.14) = .error .valueError := by native_decide
example : progImperative (.boolean true) = .ok 1 := by native_decide
example : inputSamples.all (fun x => decide (prog x = progImperative x)) = true := by
  native_decide
#eval progImperative (.integer 123)
#eval progImperative (.integer 0)
#eval progImperative (.floating 3.14)

/-! ## Loop invariant and equivalence -/

/-- The remaining contribution plus the accumulator is invariant. -/
theorem digitLoop_invariant_thm (n acc : Nat) :
    digitLoop n acc = acc + sumDigits n := by
  induction n using Nat.strong_induction_on generalizing acc with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      rw [digitLoop]
      simp [show sumDigits 0 = 0 from zero_thm]
    · rw [digitLoop]
      simp only [hn, ↓reduceDIte, Id.run, pure]
      rw [ih (n / 10) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)),
        step_thm n (Nat.pos_of_ne_zero hn)]
      omega

theorem sumDigits_equivalence_thm (n : Nat) :
    sumDigits n = sumDigitsImperative n := by
  simpa [sumDigitsImperative] using (digitLoop_invariant_thm n 0).symm

/-- Functional and imperative programs agree on all inputs, including errors. -/
theorem equivalence_thm (x : Input) : prog x = progImperative x := by
  unfold prog progImperative
  cases asNat x with
  | none => rfl
  | some n => simpa using congrArg (Except.ok (ε := Error)) (sumDigits_equivalence_thm n)

end MySumDigits
end Agent
