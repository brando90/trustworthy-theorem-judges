import Mathlib

/-!
# Sum of decimal digits

This file formalizes the Python program `prog`. The arithmetic uses unbounded
`Int` and `Nat`. `PythonInput` records the observations needed by `isinstance`:
integers (including integer subclasses), booleans, floats, and other objects.
Python booleans are integers with values zero and one. All floats and all other
objects are rejected, as are negative integers. `Except` records the `ValueError`
exception class; its diagnostic message is not part of the result model.

The functional implementation repeatedly divides by ten. Its specification uses
Mathlib's decimal digit list, independently of that implementation. A terminating
imperative loop with mutable remainder and accumulator is proved equivalent.
-/

namespace MySumDigits

/- Implementation. -/

inductive PythonInput where
  | int (value : Int)
  | bool (value : Bool)
  | float (value : Float)
  | other (description : String)
  deriving Repr

inductive PythonError where
  | valueError
  deriving DecidableEq, Repr

deriving instance DecidableEq for Except

/-- The integer value observed by Python's `isinstance(n, int)`. -/
def asInt : PythonInput → Option Int
  | .int n => some n
  | .bool b => some (if b then 1 else 0)
  | .float _ => none
  | .other _ => none

/-- The quotient is strictly smaller at every nonzero recursive call. -/
def sumDigits (n : Nat) : Nat :=
  if hn : n = 0 then 0
  else n % 10 + sumDigits (n / 10)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)

/-- A successful Python result is a nonnegative integer; failure is `ValueError`. -/
def prog (x : PythonInput) : Except PythonError Nat :=
  match asInt x with
  | some n => if 0 ≤ n then .ok (sumDigits n.toNat) else .error .valueError
  | none => .error .valueError

/- Unit tests, including the two original invalid inputs. -/

example : prog (.int 123) = .ok 6 := by native_decide
example : prog (.int 0) = .ok 0 := by native_decide
example : prog (.int 7) = .ok 7 := by native_decide
example : prog (.int 10020) = .ok 3 := by native_decide
example : prog (.int 999999) = .ok 54 := by native_decide
example : prog (.int (-1)) = .error .valueError := by native_decide
example : prog (.float 3.14) = .error .valueError := by native_decide
example : prog (.float 3.0) = .error .valueError := by native_decide
example : prog (.bool false) = .ok 0 := by native_decide
example : prog (.bool true) = .ok 1 := by native_decide
example : prog (.other "None") = .error .valueError := by native_decide

#eval prog (.int 123)
#eval prog (.int 0)
#eval prog (.int (-1))
#eval prog (.float 3.14)

/- Precondition. -/

/-- Exactly Python's `isinstance(n, int) and n >= 0`. -/
def Pre (x : PythonInput) : Prop :=
  match asInt x with
  | some n => 0 ≤ n
  | none => False

/- Properties and their proofs. Each result property takes the input and output. -/

def digits_prop (n result : Nat) : Prop :=
  result = (Nat.digits 10 n).sum

theorem digits_thm (n : Nat) : digits_prop n (sumDigits n) := by
  unfold digits_prop
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp [sumDigits]
    · rw [sumDigits, dif_neg hn,
        Nat.digits_eq_cons_digits_div (by decide) hn, List.sum_cons]
      rw [ih (n / 10) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))]

/-- This includes the zero edge case and positivity for every positive input. -/
def zero_prop (n result : Nat) : Prop :=
  result = 0 ↔ n = 0

theorem zero_thm (n : Nat) : zero_prop n (sumDigits n) := by
  unfold zero_prop
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp [sumDigits]
    · rw [sumDigits, dif_neg hn]
      have hsmall := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide : 1 < 10)
      have hdecimal := Nat.mod_add_div n 10
      constructor
      · intro hsum
        have htail : sumDigits (n / 10) = 0 := by omega
        have hquotient : n / 10 = 0 := (ih (n / 10) hsmall).mp htail
        omega
      · intro hzero
        exact (hn hzero).elim

def singleDigit_prop (n result : Nat) : Prop :=
  n < 10 → result = n

theorem singleDigit_thm (n : Nat) : singleDigit_prop n (sumDigits n) := by
  intro hlt
  by_cases hn : n = 0
  · subst n
    simp [sumDigits]
  · rw [digits_thm n, Nat.digits_of_lt 10 n hn hlt]
    simp

/-- Removing the last decimal digit gives the recursive digit-sum equation. -/
def recurrence_prop (n result : Nat) : Prop :=
  0 < n → result = n % 10 + sumDigits (n / 10)

theorem recurrence_thm (n : Nat) : recurrence_prop n (sumDigits n) := by
  intro hn
  rw [sumDigits, dif_neg (Nat.ne_of_gt hn)]

def bounds_prop (n result : Nat) : Prop :=
  0 ≤ result ∧ result ≤ n

theorem bounds_thm (n : Nat) : bounds_prop n (sumDigits n) := by
  constructor
  · exact Nat.zero_le _
  · rw [digits_thm n]
    exact Nat.digit_sum_le 10 n

def modNine_prop (n result : Nat) : Prop :=
  result % 9 = n % 9

theorem modNine_thm (n : Nat) : modNine_prop n (sumDigits n) := by
  unfold modNine_prop
  rw [digits_thm n]
  exact (Nat.modEq_nine_digits_sum n).symm

/-- There is an error exactly when the Python precondition fails. -/
def rejection_prop (x : PythonInput) : Prop :=
  prog x = .error .valueError ↔ ¬ Pre x

theorem rejection_thm (x : PythonInput) : rejection_prop x := by
  cases hx : asInt x with
  | none => simp [rejection_prop, prog, Pre, hx]
  | some n =>
    by_cases hn : 0 ≤ n <;> simp [rejection_prop, prog, Pre, hx, hn]

/- Postcondition: successful output and the conjunction of all result properties. -/

def Post_prop (x : PythonInput) (output : Except PythonError Nat) : Prop :=
  Pre x ∧
  match asInt x, output with
  | some n, .ok result =>
      digits_prop n.toNat result ∧
      zero_prop n.toNat result ∧
      singleDigit_prop n.toNat result ∧
      recurrence_prop n.toNat result ∧
      bounds_prop n.toNat result ∧
      modNine_prop n.toNat result
  | _, _ => False

/- Property-based tests. These checks supply evidence in addition to the proofs. -/

-- PBT for digits_prop: randomized inputs and exhaustive small inputs.
#eval Plausible.Testable.check
  (∀ n : Nat, sumDigits n = (Nat.digits 10 n).sum)
example : (List.range 1000).all
    (fun n => decide (sumDigits n = (Nat.digits 10 n).sum)) = true := by native_decide

-- PBT for zero_prop.
example : (List.range 1000).all
    (fun n => decide (sumDigits n = 0 ↔ n = 0)) = true := by native_decide

-- PBT for singleDigit_prop: every admissible single digit is included.
example : (List.range 1000).all
    (fun n => decide (n < 10 → sumDigits n = n)) = true := by native_decide

-- PBT for recurrence_prop, including the zero boundary of the implication.
example : (List.range 1000).all
    (fun n => decide (0 < n → sumDigits n = n % 10 + sumDigits (n / 10))) = true := by
  native_decide

-- PBT for bounds_prop.
example : (List.range 1000).all
    (fun n => decide (0 ≤ sumDigits n ∧ sumDigits n ≤ n)) = true := by native_decide

-- PBT for modNine_prop.
#eval Plausible.Testable.check (∀ n : Nat, sumDigits n % 9 = n % 9)
example : (List.range 1000).all
    (fun n => decide (sumDigits n % 9 = n % 9)) = true := by native_decide

/-- Bounded signed integers, both booleans, many floats, and other Python objects. -/
def inputSamples : List PythonInput :=
  (List.range 401).map (fun k => .int ((k : Int) - 200)) ++
  [.bool false, .bool true, .float 3.14, .float (-0.0),
    .float (1.0 / 0.0), .float (0.0 / 0.0), .other "None", .other "'123'", .other "[]"] ++
  (List.range 101).map (fun k => .float (Float.ofNat k / 10.0))

-- PBT for rejection_prop. Floats are checked by their type tag, without arithmetic.
example : inputSamples.all (fun x =>
    match asInt x with
    | some n => decide (prog x = .error .valueError ↔ ¬ (0 ≤ n))
    | none => decide (prog x = .error .valueError)) = true := by native_decide

/-- An executable form of the entire postcondition, evaluated on `prog`. -/
def postCheck (x : PythonInput) : Bool :=
  match asInt x, prog x with
  | some n, .ok result => decide (
      0 ≤ n ∧
      result = (Nat.digits 10 n.toNat).sum ∧
      (result = 0 ↔ n.toNat = 0) ∧
      (n.toNat < 10 → result = n.toNat) ∧
      (0 < n.toNat → result = n.toNat % 10 + sumDigits (n.toNat / 10)) ∧
      (0 ≤ result ∧ result ≤ n.toNat) ∧
      result % 9 = n.toNat % 9)
  | _, _ => false

/-- The bounded postcondition test checks precisely `Post_prop`. -/
theorem postCheck_spec (x : PythonInput) :
    postCheck x = true ↔ Post_prop x (prog x) := by
  cases hx : asInt x with
  | none => simp [postCheck, Post_prop, Pre, hx]
  | some n =>
    cases hr : prog x <;>
      simp only [postCheck, Post_prop, Pre, hx, hr, digits_prop, zero_prop,
        singleDigit_prop, recurrence_prop, bounds_prop, modNine_prop,
        decide_eq_true_eq, Bool.false_eq_true, and_false]

-- PBT for Post_prop over 1000 admissible integers and both admissible booleans.
example : ((List.range 1000).map (fun n => PythonInput.int n) ++
    [PythonInput.bool false, PythonInput.bool true]).all postCheck = true := by native_decide

-- PBT for the precondition implication on the mixed valid/invalid input sample.
example : inputSamples.all (fun x =>
    match asInt x with
    | some n => decide (0 ≤ n → postCheck x = true)
    | none => true) = true := by native_decide

/- Correctness for every input satisfying the Python precondition. -/

theorem correctness_thm (x : PythonInput) (hpre : Pre x) : Post_prop x (prog x) := by
  refine ⟨hpre, ?_⟩
  cases hx : asInt x with
  | none => simp [Pre, hx] at hpre
  | some n =>
    have hn : 0 ≤ n := by simpa [Pre, hx] using hpre
    simp only [prog, hx, if_pos hn]
    exact ⟨digits_thm n.toNat, zero_thm n.toNat, singleDigit_thm n.toNat,
      recurrence_thm n.toNat, bounds_thm n.toNat, modNine_thm n.toNat⟩

/- Imperative implementation.

The recursive call is the loop back edge. Giving its decreasing remainder
explicitly makes the Python while loop total and available to kernel proofs.
Each iteration performs the same two assignments, in the same order, as Python.
-/

def digitLoop (remaining accumulator : Nat) : Nat := Id.run do
  let mut n := remaining
  let mut total := accumulator
  if hn : n = 0 then
    return total
  else
    total := total + n % 10
    n := n / 10
    return digitLoop n total
termination_by remaining
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)

def sumDigitsImperative (n : Nat) : Nat := Id.run do
  let mut total := 0
  total := digitLoop n total
  return total

def progImperative (x : PythonInput) : Except PythonError Nat := Id.run do
  match asInt x with
  | none => return .error .valueError
  | some n =>
    if n < 0 then
      return .error .valueError
    let mut total := 0
    total := sumDigitsImperative n.toNat
    return .ok total

/- Imperative tests. -/

example : progImperative (.int 123) = .ok 6 := by native_decide
example : progImperative (.int 0) = .ok 0 := by native_decide
example : progImperative (.int 10020) = .ok 3 := by native_decide
example : progImperative (.int (-1)) = .error .valueError := by native_decide
example : progImperative (.float 3.14) = .error .valueError := by native_decide
example : progImperative (.bool true) = .ok 1 := by native_decide
#eval progImperative (.int 123)
#eval progImperative (.float 3.14)

example : (List.range 1000).all
    (fun n => sumDigits n == sumDigitsImperative n) = true := by native_decide
example : inputSamples.all
    (fun x => decide (prog x = progImperative x)) = true := by native_decide

-- PBT for the accumulator invariant, including nonzero initial accumulators.
example : (List.range 200).all (fun n => (List.range 30).all
    (fun total => digitLoop n total == total + sumDigits n)) = true := by native_decide

/- The accumulator invariant proves functional/imperative equivalence. -/

theorem digitLoop_invariant (n total : Nat) :
    digitLoop n total = total + sumDigits n := by
  induction n using Nat.strong_induction_on generalizing total with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp [digitLoop, sumDigits]
    · rw [digitLoop]
      simp only [hn, ↓reduceDIte, Id.run, pure]
      rw [ih (n / 10) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))]
      rw [recurrence_thm n (Nat.pos_of_ne_zero hn)]
      omega

theorem sumDigits_equivalence_thm (n : Nat) :
    sumDigits n = sumDigitsImperative n := by
  simpa [sumDigitsImperative] using (digitLoop_invariant n 0).symm

/-- Equivalence includes every invalid input, not only inputs satisfying `Pre`. -/
theorem equivalence_thm (x : PythonInput) : prog x = progImperative x := by
  cases hx : asInt x with
  | none => simp [prog, progImperative, hx]
  | some n =>
    by_cases hn : 0 ≤ n
    · simp [prog, progImperative, hx, hn, not_lt.mpr hn, sumDigits_equivalence_thm]
    · simp [prog, progImperative, hx, hn, lt_of_not_ge hn]

end MySumDigits
