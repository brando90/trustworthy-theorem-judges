import Mathlib

/-!
# Sum of the decimal digits of a non-negative Python integer

`sumDigits` follows the repeated remainder/division algorithm. `Input` models
Python's run-time type check: integers and booleans (a Python subclass of int)
are distinguished from floats and other non-integer objects. `Except` models
raising `ValueError`; the error message's presentation is not part of the model.
The result is a `Nat`, since a successful Python result is always non-negative.

The specification uses Mathlib's decimal digits, independently of the loop.
The imperative version is a well-founded, tail-recursive while loop: each body
uses `Id.run` and mutable state, and recurs precisely while the remainder is
positive. Thus there is no fuel bound or truncation of large integers.
-/

namespace MySumDigits

deriving instance DecidableEq for Except

/-! ## Functional implementation -/

inductive Input where
  | integer (value : Int)
  | boolean (value : Bool)
  | floating (value : Float)
  | other (description : String)
  deriving Repr

inductive Error where
  | valueError
  deriving Repr, DecidableEq, BEq

/-- The successful value of Python's non-negative-integer check. -/
def inputNat? : Input → Option Nat
  | .integer z => if 0 ≤ z then some z.toNat else none
  | .boolean b => some (if b then 1 else 0)
  | .floating _ => none
  | .other _ => none

/-- Repeatedly consume the least significant decimal digit. -/
def sumDigits (n : Nat) : Nat :=
  if h : n = 0 then 0 else n % 10 + sumDigits (n / 10)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

def prog (x : Input) : Except Error Nat :=
  match inputNat? x with
  | none => .error .valueError
  | some n => .ok (sumDigits n)

/-! ## Unit tests -/

example : prog (.integer 123) = .ok 6 := by native_decide
example : prog (.integer 0) = .ok 0 := by native_decide
example : prog (.integer 7) = .ok 7 := by native_decide
example : prog (.integer 1002003) = .ok 6 := by native_decide
example : prog (.integer (-1)) = .error .valueError := by native_decide
example : prog (.floating 3.14) = .error .valueError := by native_decide
example : prog (.floating 3.0) = .error .valueError := by native_decide
example : prog (.boolean true) = .ok 1 := by native_decide
example : prog (.boolean false) = .ok 0 := by native_decide
example : prog (.other "123") = .error .valueError := by native_decide

#eval prog (.integer 123)
#eval prog (.integer 0)
#eval prog (.integer (-1))
#eval prog (.floating 3.14)

/-! ## Preconditions and properties -/

/-- Exactly `isinstance(n, int) and n >= 0`, including Python booleans. -/
def Pre : Input → Prop
  | .integer z => 0 ≤ z
  | .boolean _ => True
  | .floating _ => False
  | .other _ => False

theorem pre_iff_inputNat_thm (x : Input) :
    Pre x ↔ ∃ n, inputNat? x = some n := by
  cases x with
  | integer z =>
      by_cases h : 0 ≤ z <;> simp [Pre, inputNat?, h]
  | boolean b => simp [Pre, inputNat?]
  | floating f => simp [Pre, inputNat?]
  | other s => simp [Pre, inputNat?]

/-- Exact mathematical specification, not merely an upper bound. -/
def digits_prop (n : Nat) : Prop :=
  sumDigits n = (Nat.digits 10 n).sum

theorem digits_thm (n : Nat) : digits_prop n := by
  unfold digits_prop
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · simp [hn, sumDigits, Nat.digits_zero]
      · rw [sumDigits, dif_neg hn,
          Nat.digits_eq_cons_digits_div (by decide : 1 < 10) hn]
        simp only [List.sum_cons]
        rw [ih (n / 10) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))]

def zero_prop : Prop := sumDigits 0 = 0

theorem zero_thm : zero_prop := by
  simp [zero_prop, sumDigits]

def singleDigit_prop (n : Nat) : Prop := n < 10 → sumDigits n = n

theorem singleDigit_thm (n : Nat) : singleDigit_prop n := by
  intro hn
  rw [sumDigits]
  split_ifs with hz
  · exact hz.symm
  · simp [Nat.mod_eq_of_lt hn, Nat.div_eq_of_lt hn, show sumDigits 0 = 0 from zero_thm]

def step_prop (n : Nat) : Prop :=
  0 < n → sumDigits n = n % 10 + sumDigits (n / 10)

theorem step_thm (n : Nat) : step_prop n := by
  intro hn
  rw [sumDigits, dif_neg (Nat.ne_of_gt hn)]

def bounds_prop (n : Nat) : Prop := 0 ≤ sumDigits n ∧ sumDigits n ≤ n

theorem bounds_thm (n : Nat) : bounds_prop n := by
  constructor
  · exact Nat.zero_le _
  · rw [show sumDigits n = (Nat.digits 10 n).sum from digits_thm n]
    exact Nat.digit_sum_le 10 n

def zeroIff_prop (n : Nat) : Prop := sumDigits n = 0 ↔ n = 0

theorem zeroIff_thm (n : Nat) : zeroIff_prop n := by
  unfold zeroIff_prop
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · simp [hn, show sumDigits 0 = 0 from zero_thm]
      · have hlt : n / 10 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
        rw [step_thm n (Nat.pos_of_ne_zero hn)]
        have hi := ih (n / 10) hlt
        have hdecomp := Nat.mod_add_div n 10
        constructor
        · intro hsum
          have hq : n / 10 = 0 := hi.mp (by omega)
          omega
        · intro hzero
          exact False.elim (hn hzero)

def modNine_prop (n : Nat) : Prop := sumDigits n % 9 = n % 9

theorem modNine_thm (n : Nat) : modNine_prop n := by
  unfold modNine_prop
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · simp [hn, show sumDigits 0 = 0 from zero_thm]
      · rw [step_thm n (Nat.pos_of_ne_zero hn), Nat.add_mod,
          ih (n / 10) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))]
        have hdecomp := Nat.mod_add_div n 10
        omega

/-- Both directions matter: valid inputs never raise, invalid ones always do. -/
def validation_prop (x : Input) : Prop :=
  prog x = .error .valueError ↔ ¬ Pre x

theorem validation_thm (x : Input) : validation_prop x := by
  unfold validation_prop
  rw [pre_iff_inputNat_thm]
  cases h : inputNat? x <;> simp [prog, h]

/-! ## Postcondition -/

/-- A successful result is exactly the digit sum, with the advertised edge
cases and useful numerical consequences. The original input is retained. -/
def Post_prop (x : Input) : Prop :=
  ∃ n, inputNat? x = some n ∧
    prog x = .ok ((Nat.digits 10 n).sum) ∧
    digits_prop n ∧ zero_prop ∧ singleDigit_prop n ∧ step_prop n ∧
    bounds_prop n ∧ zeroIff_prop n ∧ modNine_prop n

/-! ## Property-based tests

These are exhaustive bounded Boolean checks, not proofs of the universal
properties. Every executable `_prop`, including the postcondition, is tested.
-/

-- PBT: digits_prop
example : (List.range 1000).all (fun n =>
    decide (sumDigits n = (Nat.digits 10 n).sum)) = true := by native_decide

-- PBT: zero_prop (the property has no variable input)
example : (List.range 100).all (fun _ => decide (sumDigits 0 = 0)) = true := by
  native_decide

-- PBT: singleDigit_prop
example : (List.range 1000).all (fun n =>
    decide (n < 10 → sumDigits n = n)) = true := by native_decide

-- PBT: step_prop
example : (List.range 1000).all (fun n =>
    decide (0 < n → sumDigits n = n % 10 + sumDigits (n / 10))) = true := by
  native_decide

-- PBT: bounds_prop
example : (List.range 1000).all (fun n =>
    decide (0 ≤ sumDigits n ∧ sumDigits n ≤ n)) = true := by native_decide

-- PBT: zeroIff_prop
example : (List.range 1000).all (fun n =>
    decide (sumDigits n = 0 ↔ n = 0)) = true := by native_decide

-- PBT: modNine_prop
example : (List.range 1000).all (fun n =>
    decide (sumDigits n % 9 = n % 9)) = true := by native_decide

/-- Deliberately include valid and invalid integer values and non-integer types. -/
def inputSamples : List Input :=
  (List.range 401).map (fun n => .integer ((n : Int) - 100)) ++
  [.boolean false, .boolean true, .floating 3.14, .floating 3.0,
   .floating (-1.0), .floating 0.0, .other "123", .other "None"]

def preCheck : Input → Bool
  | .integer z => decide (0 ≤ z)
  | .boolean _ => true
  | .floating _ => false
  | .other _ => false

-- PBT: validation_prop, including floats even when numerically integral.
example : inputSamples.all (fun x =>
    decide (prog x = .error .valueError) == !preCheck x) = true := by native_decide

/-- Executable form of the entire postcondition. The match supplies the
existential witness, without requiring an unbounded existential decision. -/
def postCheck (x : Input) : Bool :=
  match inputNat? x with
  | none => false
  | some n => decide (
      prog x = .ok ((Nat.digits 10 n).sum) ∧
      sumDigits n = (Nat.digits 10 n).sum ∧ sumDigits 0 = 0 ∧
      (n < 10 → sumDigits n = n) ∧
      (0 < n → sumDigits n = n % 10 + sumDigits (n / 10)) ∧
      (0 ≤ sumDigits n ∧ sumDigits n ≤ n) ∧
      (sumDigits n = 0 ↔ n = 0) ∧ sumDigits n % 9 = n % 9)

-- PBT: Post_prop, restricted to exactly the admissible inputs.
example : inputSamples.all (fun x => !preCheck x || postCheck x) = true := by
  native_decide
example : (List.range 1000).all (fun n => postCheck (.integer n)) = true := by
  native_decide

#eval inputSamples.all (fun x => !preCheck x || postCheck x)

/-! ## Correctness -/

theorem correctness_thm (x : Input) (hx : Pre x) : Post_prop x := by
  obtain ⟨n, hn⟩ := (pre_iff_inputNat_thm x).mp hx
  refine ⟨n, hn, ?_, digits_thm n, zero_thm, singleDigit_thm n,
    step_thm n, bounds_thm n, zeroIff_thm n, modNine_thm n⟩
  simp [prog, hn, show sumDigits n = (Nat.digits 10 n).sum from digits_thm n]

/-! ## Imperative implementation -/

/-- One mutable while-loop body, followed by a tail call if the guard holds.
The decreasing remaining integer certifies termination of the unbounded loop. -/
def digitLoop (n total : Nat) : Nat := Id.run do
  let mut remaining := n
  let mut acc := total
  if h : 0 < remaining then
    acc := acc + remaining % 10
    remaining := remaining / 10
    return digitLoop remaining acc
  else
    return acc
termination_by n
decreasing_by exact Nat.div_lt_self h (by decide)

def sumDigitsImperative (n : Nat) : Nat := Id.run do
  let mut total := 0
  total := digitLoop n total
  return total

def progImperative (x : Input) : Except Error Nat := Id.run do
  match inputNat? x with
  | none => return .error .valueError
  | some n =>
      let mut total := 0
      total := digitLoop n total
      return .ok total

/-! ## Imperative tests -/

example : progImperative (.integer 123) = .ok 6 := by native_decide
example : progImperative (.integer 0) = .ok 0 := by native_decide
example : progImperative (.integer (-1)) = .error .valueError := by native_decide
example : progImperative (.floating 3.14) = .error .valueError := by native_decide
example : progImperative (.boolean true) = .ok 1 := by native_decide
example : (List.range 1000).all (fun n =>
    decide (sumDigits n = sumDigitsImperative n)) = true := by native_decide
example : inputSamples.all (fun x =>
    decide (prog x = progImperative x)) = true := by native_decide

#eval progImperative (.integer 123)
#eval progImperative (.integer 1002003)

/-! ## Loop invariant and equivalence -/

/-- The accumulated total plus the sum of unprocessed digits is invariant. -/
theorem digitLoop_invariant_thm (n total : Nat) :
    digitLoop n total = total + sumDigits n := by
  induction n using Nat.strong_induction_on generalizing total with
  | h n ih =>
      by_cases hn : 0 < n
      · rw [digitLoop]
        simp only [hn, ↓reduceDIte, Id.run]
        rw [ih (n / 10) (Nat.div_lt_self hn (by decide))]
        rw [step_thm n hn]
        exact Nat.add_assoc total (n % 10) (sumDigits (n / 10))
      · have hz : n = 0 := by omega
        subst n
        simp [digitLoop, show sumDigits 0 = 0 from zero_thm]

theorem sumDigits_equivalence_thm (n : Nat) :
    sumDigits n = sumDigitsImperative n := by
  simp [sumDigitsImperative, digitLoop_invariant_thm]

/-- Equivalence on all inputs, not just those satisfying the precondition. -/
theorem equivalence_thm (x : Input) : prog x = progImperative x := by
  cases h : inputNat? x <;> simp [prog, progImperative, h, digitLoop_invariant_thm]

end MySumDigits
