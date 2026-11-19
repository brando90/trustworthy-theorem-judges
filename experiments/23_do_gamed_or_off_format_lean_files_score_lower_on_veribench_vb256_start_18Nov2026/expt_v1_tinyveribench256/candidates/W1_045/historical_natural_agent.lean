import Mathlib
namespace Agent

/-!
# Counting even decimal digits

Translation of the Python `count_even_digits` program. `Input.int` represents
Python integers (including booleans, represented by 0 and 1); `Input.nonInteger`
represents the other input objects, which the program rejects without inspecting.
`Except.error` models `ValueError`, retaining its message. There is no bounded
machine-integer assumption.

The digit list is little-endian, which is immaterial to counting. Zero is
explicitly represented by the single digit 0, unlike `Nat.digits`. The exactness
specification counts the filtered, reversed list (ordinary printed order).
-/

namespace CountEvenDigits
deriving instance DecidableEq for Except

inductive Input where
  | int (value : Int)
  | nonInteger
  deriving DecidableEq, Repr

def valueError : String := "Input must be a non-negative integer"

def decimalDigits (n : Nat) : List Nat :=
  if n = 0 then [0] else Nat.digits 10 n

def evenDigit (d : Nat) : Bool := d % 2 == 0

/-- Functional version of Python's sum of one for each even digit. -/
def tally : List Nat → Nat
  | [] => 0
  | d :: ds => (if evenDigit d then 1 else 0) + tally ds

def countNat (n : Nat) : Nat := tally (decimalDigits n)

def countEvenDigits : Input → Except String Nat
  | .int z => if 0 ≤ z then .ok (countNat z.toNat) else .error valueError
  | .nonInteger => .error valueError

-- Fixed examples, including both sorts of precondition violations.
example : countEvenDigits (.int 24863) = .ok 4 := by native_decide
example : countEvenDigits (.int 0) = .ok 1 := by native_decide
example : countEvenDigits (.int 13579) = .ok 0 := by native_decide
example : countEvenDigits (.int 10020) = .ok 4 := by native_decide
example : countEvenDigits (.int (-1)) = .error valueError := by native_decide
example : countEvenDigits .nonInteger = .error valueError := by native_decide
#eval countEvenDigits (.int 24863)
#eval countEvenDigits (.int 0)
#eval countEvenDigits (.int (-1))

def Pre : Input → Prop
  | .int z => 0 ≤ z
  | .nonInteger => False

/-- The normalized digits reconstruct precisely the original integer. -/
theorem decimalDigits_value (n : Nat) : Nat.ofDigits 10 (decimalDigits n) = n := by
  by_cases h : n = 0
  · simp [decimalDigits, h]
  · simp [decimalDigits, h, Nat.ofDigits_digits]

theorem decimalDigits_bound (n d : Nat) (hd : d ∈ decimalDigits n) : d < 10 := by
  by_cases h : n = 0
  · have hd0 : d = 0 := by simpa [decimalDigits, h] using hd
    omega
  · exact Nat.digits_lt_base (by decide) (by simpa [decimalDigits, h] using hd)

theorem decimalDigits_nonempty (n : Nat) : decimalDigits n ≠ [] := by
  by_cases h : n = 0 <;>
    simp [decimalDigits, h, Nat.digits_eq_nil_iff_eq_zero]

theorem decimalDigits_single (n : Nat) (hn : n < 10) : decimalDigits n = [n] := by
  by_cases h : n = 0
  · simp [decimalDigits, h]
  · simp [decimalDigits, h, Nat.digits_of_lt 10 n h hn]

/-- Appending a digit must not introduce a fictitious leading zero. -/
theorem decimalDigits_append (n d : Nat) (hn : 0 < n) (hd : d < 10) :
    decimalDigits (10 * n + d) = d :: decimalDigits n := by
  have hn0 : n ≠ 0 := by omega
  have hs : 10 * n + d ≠ 0 := by omega
  simp only [decimalDigits, if_neg hn0, if_neg hs]
  rw [Nat.add_comm (10 * n) d, Nat.digits_add 10 (by decide) d n hd (Or.inr hn0)]

theorem tally_filter (ds : List Nat) : tally ds = (ds.filter evenDigit).length := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    by_cases h : evenDigit d = true <;>
      simp [tally, h, ih, Nat.add_comm]

theorem tally_bound (ds : List Nat) : tally ds ≤ ds.length := by
  rw [tally_filter]
  exact List.length_filter_le evenDigit ds

/-- A zero count is equivalent to every digit being odd. -/
theorem tally_zero_iff (ds : List Nat) :
    tally ds = 0 ↔ ∀ d ∈ ds, d % 2 = 1 := by
  induction ds with
  | nil => simp [tally]
  | cons d ds ih =>
    have hm : d % 2 < 2 := Nat.mod_lt d (by decide)
    by_cases h : d % 2 = 0
    · simp [tally, evenDigit, h, ih]
    · have h1 : d % 2 = 1 := by omega
      simp [tally, evenDigit, h1, ih]

/-- Exact count in the most-significant-first decimal representation. -/
def exact_prop (n : Nat) : Prop :=
  countNat n = ((decimalDigits n).reverse.filter evenDigit).length

theorem exact_thm (n : Nat) : exact_prop n := by
  simp [exact_prop, countNat, tally_filter, List.filter_reverse]

/-- The representation is nonempty, and the result cannot exceed its length.
The lower bound zero is enforced by the result type `Nat`. -/
def bounds_prop (n : Nat) : Prop :=
  0 < (decimalDigits n).length ∧ countNat n ≤ (decimalDigits n).length

theorem bounds_thm (n : Nat) : bounds_prop n := by
  constructor
  · exact List.length_pos_iff.mpr (decimalDigits_nonempty n)
  · exact tally_bound _

def zero_prop (n : Nat) : Prop := n = 0 → countNat n = 1

theorem zero_thm (n : Nat) : zero_prop n := by
  intro h
  subst n
  norm_num [countNat, decimalDigits, tally, evenDigit]

def odd_prop (n : Nat) : Prop :=
  countNat n = 0 ↔ ∀ d ∈ decimalDigits n, d % 2 = 1

theorem odd_thm (n : Nat) : odd_prop n := tally_zero_iff _

def single_digit_prop (n : Nat) : Prop :=
  n < 10 → countNat n = (if n % 2 = 0 then 1 else 0)

theorem single_digit_thm (n : Nat) : single_digit_prop n := by
  intro hn
  simp [countNat, decimalDigits_single n hn, tally, evenDigit]

/-- Decimal extension adds one exactly when the new digit is even. -/
def append_prop (n d : Nat) : Prop :=
  0 < n → d < 10 →
    countNat (10 * n + d) = countNat n + (if d % 2 = 0 then 1 else 0)

theorem append_thm (n d : Nat) : append_prop n d := by
  intro hn hd
  unfold countNat
  rw [decimalDigits_append n d hn hd]
  simp [tally, evenDigit, Nat.add_comm]

/-- The precondition characterizes success and rejection in both directions. -/
def validation_prop (x : Input) : Prop :=
  (countEvenDigits x = .error valueError ↔ ¬ Pre x) ∧
  ((∃ r, countEvenDigits x = .ok r) ↔ Pre x)

theorem validation_thm (x : Input) : validation_prop x := by
  cases x with
  | nonInteger => simp [validation_prop, Pre, countEvenDigits]
  | int z =>
    by_cases h : 0 ≤ z <;> simp [validation_prop, Pre, countEvenDigits, h]

/-- Complete contract on admissible inputs. All ten decimal extensions are
included; the stronger `append_thm` is stated for arbitrary natural `d`. -/
def Post_prop (x : Input) : Prop :=
  validation_prop x ∧
  match x with
  | .nonInteger => False
  | .int z =>
    countEvenDigits x = .ok (countNat z.toNat) ∧
    exact_prop z.toNat ∧ bounds_prop z.toNat ∧ zero_prop z.toNat ∧
    odd_prop z.toNat ∧ single_digit_prop z.toNat ∧
    ∀ d ∈ List.range 10, append_prop z.toNat d

/-! ## Property-based tests
These are executable Boolean versions, not theorem proofs. The lists cover
zero, both parities, interior/trailing zeros, and changes in decimal length.
-/

def exactCheck (n : Nat) : Bool :=
  countNat n == ((decimalDigits n).reverse.filter evenDigit).length

def boundsCheck (n : Nat) : Bool :=
  decide (0 < (decimalDigits n).length) &&
  decide (countNat n ≤ (decimalDigits n).length)

def zeroCheck (n : Nat) : Bool := (n != 0) || (countNat n == 1)

def oddCheck (n : Nat) : Bool :=
  (countNat n == 0) == (decimalDigits n).all (fun d => d % 2 == 1)

def singleDigitCheck (n : Nat) : Bool :=
  decide (10 ≤ n) || (countNat n == if evenDigit n then 1 else 0)

def appendCheck (n d : Nat) : Bool :=
  (n == 0) || decide (10 ≤ d) ||
  (countNat (10 * n + d) == countNat n + if evenDigit d then 1 else 0)

def preCheck : Input → Bool
  | .int z => decide (0 ≤ z)
  | .nonInteger => false

def validationCheck (x : Input) : Bool :=
  (decide (countEvenDigits x = .error valueError) == !preCheck x) &&
  ((match countEvenDigits x with | .ok _ => true | .error _ => false) == preCheck x)

def postCheck (x : Input) : Bool :=
  validationCheck x &&
  match x with
  | .nonInteger => false
  | .int z =>
    let n := z.toNat
    decide (countEvenDigits x = .ok (countNat n)) &&
    exactCheck n && boundsCheck n && zeroCheck n && oddCheck n &&
    singleDigitCheck n && (List.range 10).all (appendCheck n)

-- PBT for exact_prop.
example : (List.range 2000).all exactCheck = true := by native_decide
-- PBT for bounds_prop.
example : (List.range 2000).all boundsCheck = true := by native_decide
-- PBT for zero_prop.
example : (List.range 2000).all zeroCheck = true := by native_decide
-- PBT for odd_prop.
example : (List.range 2000).all oddCheck = true := by native_decide
-- PBT for single_digit_prop (also exercises the implication outside its premise).
example : (List.range 100).all singleDigitCheck = true := by native_decide
-- PBT for append_prop, including n = 0 and non-digit d values.
example : (List.range 300).all (fun n => (List.range 15).all (appendCheck n)) = true := by
  native_decide

def validationInputs : List Input :=
  .nonInteger :: (List.range 401).map (fun n => .int ((n : Int) - 200))

-- PBT for validation_prop: valid, negative, and non-integer inputs.
example : validationInputs.all validationCheck = true := by native_decide
-- PBT for Post_prop under precisely Pre, not a stronger restriction.
example : validationInputs.all (fun x => !preCheck x || postCheck x) = true := by
  native_decide
example : (List.range 2000).all (fun n => postCheck (.int (n : Int))) = true := by
  native_decide
#eval (List.range 1000).all exactCheck
#eval validationInputs.all validationCheck
#eval (List.range 1000).all (fun n => postCheck (.int (n : Int)))

/-- Correctness includes the link from the original integer input to its result. -/
theorem correctness (x : Input) (h : Pre x) : Post_prop x := by
  refine ⟨validation_thm x, ?_⟩
  cases x with
  | nonInteger => exact h.elim
  | int z =>
    have hz : 0 ≤ z := h
    refine ⟨by simp [countEvenDigits, hz], exact_thm _, bounds_thm _, zero_thm _,
      odd_thm _, single_digit_thm _, ?_⟩
    intro d hd
    exact append_thm _ _

/-! ## Imperative version -/

/-- Mutable accumulator and an actual `for` loop, without calling `tally`. -/
def tallyImperative (ds : List Nat) (initial : Nat := 0) : Nat := Id.run do
  let mut acc := initial
  for d in ds do
    if evenDigit d then
      acc := acc + 1
  return acc

def countEvenDigitsImperative (x : Input) : Except String Nat := Id.run do
  match x with
  | .nonInteger => return .error valueError
  | .int z =>
    if z < 0 then
      return .error valueError
    else
      let result := tallyImperative (decimalDigits z.toNat)
      return .ok result

example : countEvenDigitsImperative (.int 24863) = .ok 4 := by native_decide
example : countEvenDigitsImperative (.int 0) = .ok 1 := by native_decide
example : countEvenDigitsImperative (.int 13579) = .ok 0 := by native_decide
example : countEvenDigitsImperative (.int (-1)) = .error valueError := by native_decide
example : countEvenDigitsImperative .nonInteger = .error valueError := by native_decide
#eval countEvenDigitsImperative (.int 24863)
#eval countEvenDigitsImperative (.int 0)
#eval countEvenDigitsImperative (.int (-1))
example : validationInputs.all (fun x =>
    decide (countEvenDigits x = countEvenDigitsImperative x)) = true := by native_decide

/-- Loop invariant, generalized over every possible initial accumulator. -/
theorem tallyImperative_eq (ds : List Nat) (initial : Nat) :
    tallyImperative ds initial = initial + tally ds := by
  induction ds generalizing initial with
  | nil => simp [tallyImperative, tally]
  | cons d ds ih =>
    by_cases h : evenDigit d = true
    · simpa [tallyImperative, tally, List.forIn_cons, h, Nat.add_assoc] using ih (initial + 1)
    · simpa [tallyImperative, tally, List.forIn_cons, h] using ih initial

/-- Equivalence also covers errors, so it has no precondition. -/
theorem functional_eq_imperative (x : Input) :
    countEvenDigits x = countEvenDigitsImperative x := by
  cases x with
  | nonInteger => rfl
  | int z =>
    by_cases h : 0 ≤ z
    · have hn : ¬ z < 0 := by omega
      simp [countEvenDigits, countEvenDigitsImperative, h, hn, tallyImperative_eq, countNat]
    · have hn : z < 0 := by omega
      simp [countEvenDigits, countEvenDigitsImperative, h, hn]

end CountEvenDigits
end Agent
