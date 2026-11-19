import Mathlib
namespace Agent

/-!
# Python's signed Euclidean greatest common divisor

This file models arbitrary Python integers by `Int`.  Python uses floor
remainder, represented by `Int.fmod`, so a nonzero result has the sign of the
last nonzero divisor (or is the original first input when the divisor is zero).
In particular this program does not always return the nonnegative normalized
GCD.  Termination is justified by the decreasing absolute value of the divisor.
-/

namespace humaneval_13__gcd

/-- The remainder used by Python's `%` on integers. -/
def pythonMod (a b : Int) : Int := a.fmod b

/-- Each nonterminal iteration strictly decreases the absolute divisor. -/
lemma pythonMod_lt (a b : Int) (hb : b ≠ 0) :
    (pythonMod a b).natAbs < b.natAbs := by
  unfold pythonMod
  by_cases hp : 0 < b
  · exact Int.natAbs_lt_natAbs_of_nonneg_of_lt
      (Int.fmod_nonneg_of_pos a hp) (Int.fmod_lt_of_pos a hp)
  · have hn : 0 < -b := by omega
    have h := Int.natAbs_lt_natAbs_of_nonneg_of_lt
      (Int.fmod_nonneg_of_pos (-a) hn) (Int.fmod_lt_of_pos (-a) hn)
    simpa only [Int.neg_fmod_neg, Int.natAbs_neg] using h

/-- Functional translation of `while b: a, b = b, a % b`. -/
def greatest_common_divisor (a b : Int) : Int :=
  if _hb : b = 0 then a
  else greatest_common_divisor b (pythonMod a b)
termination_by b.natAbs
decreasing_by exact pythonMod_lt a b _hb

-- Unit tests from the Python doctests and test suite.
example : greatest_common_divisor 3 5 = 1 := by native_decide
example : greatest_common_divisor 25 15 = 5 := by native_decide
example : greatest_common_divisor 0 1 = 1 := by native_decide
example : greatest_common_divisor 2 0 = 2 := by native_decide
example : greatest_common_divisor 0 0 = 0 := by native_decide
example : greatest_common_divisor 3 7 = 1 := by native_decide
example : greatest_common_divisor 10 15 = 5 := by native_decide
example : greatest_common_divisor 49 14 = 7 := by native_decide
example : greatest_common_divisor 144 60 = 12 := by native_decide
-- Signed cases distinguish Python's algorithm from normalized GCD.
example : greatest_common_divisor 10 (-15) = -5 := by native_decide
example : greatest_common_divisor (-10) 15 = 5 := by native_decide
example : greatest_common_divisor (-10) (-15) = -5 := by native_decide
example : greatest_common_divisor (-7) 0 = -7 := by native_decide
example : greatest_common_divisor 0 (-7) = -7 := by native_decide
#eval greatest_common_divisor 144 60
#eval greatest_common_divisor 10 (-15)

/-- Python accepts all pairs of integers; there are no input restrictions. -/
def Pre (_a _b : Int) : Prop := True

/-- The absolute value is the usual nonnegative mathematical GCD. -/
def magnitude_prop (a b r : Int) : Prop := r.natAbs = Int.gcd a b

theorem magnitude_thm (a b : Int) :
    magnitude_prop a b (greatest_common_divisor a b) := by
  unfold magnitude_prop
  rw [greatest_common_divisor]
  split_ifs with hb
  · subst b
    simp
  · have ih := magnitude_thm b (pythonMod a b)
    unfold magnitude_prop at ih
    rw [ih]
    simp [pythonMod, Int.fmod_def, Int.gcd_comm]
termination_by b.natAbs
decreasing_by exact pythonMod_lt a b hb

/-- A nonzero Python remainder has the divisor's sign. -/
lemma pythonMod_sign (a b : Int) (hb : b ≠ 0) (hr : pythonMod a b ≠ 0) :
    (pythonMod a b).sign = b.sign := by
  by_cases hp : 0 < b
  · have h : 0 ≤ pythonMod a b := Int.fmod_nonneg_of_pos a hp
    rw [Int.sign_eq_one_iff_pos.mpr (by omega : 0 < pythonMod a b),
      Int.sign_eq_one_iff_pos.mpr hp]
  · have hn : b < 0 := by omega
    have h := Int.fmod_nonneg_of_pos (-a) (b := -b) (by omega)
    rw [Int.neg_fmod_neg] at h
    have hr' : a.fmod b ≠ 0 := hr
    have hneg : pythonMod a b < 0 := by unfold pythonMod; omega
    rw [Int.sign_eq_neg_one_iff_neg.mpr hneg,
      Int.sign_eq_neg_one_iff_neg.mpr hn]

/-- The result's sign follows the initial divisor, except in the base case. -/
def sign_prop (a b r : Int) : Prop :=
  r.sign = if b = 0 then a.sign else b.sign

theorem sign_thm (a b : Int) :
    sign_prop a b (greatest_common_divisor a b) := by
  unfold sign_prop
  rw [greatest_common_divisor]
  split_ifs with hb
  · rfl
  · by_cases hr : pythonMod a b = 0
    · rw [hr, greatest_common_divisor]
      simp
    · have ih := sign_thm b (pythonMod a b)
      unfold sign_prop at ih
      rw [if_neg hr] at ih
      exact ih.trans (pythonMod_sign a b hb hr)
termination_by b.natAbs
decreasing_by exact pythonMod_lt a b hb

/-- An exact closed specification, including negative inputs. -/
def signed_value_prop (a b r : Int) : Prop :=
  r = if b = 0 then a else b.sign * (Int.gcd a b : Int)

theorem signed_value_thm (a b : Int) :
    signed_value_prop a b (greatest_common_divisor a b) := by
  unfold signed_value_prop
  by_cases hb : b = 0
  · subst b
    rw [greatest_common_divisor]
    simp
  · rw [if_neg hb]
    have hs := sign_thm a b
    unfold sign_prop at hs
    rw [if_neg hb] at hs
    have hm : (greatest_common_divisor a b).natAbs = Int.gcd a b :=
      magnitude_thm a b
    calc
      greatest_common_divisor a b =
          (greatest_common_divisor a b).sign *
            ((greatest_common_divisor a b).natAbs : Int) :=
        (Int.sign_mul_natAbs _).symm
      _ = b.sign * (Int.gcd a b : Int) := by rw [hs, hm]

/-- The returned integer divides both inputs. -/
def common_divisor_prop (a b r : Int) : Prop := r ∣ a ∧ r ∣ b

theorem common_divisor_thm (a b : Int) :
    common_divisor_prop a b (greatest_common_divisor a b) := by
  have hm : (greatest_common_divisor a b).natAbs = Int.gcd a b := magnitude_thm a b
  constructor
  · apply Int.natAbs_dvd.mp
    rw [hm]
    exact Int.gcd_dvd_left a b
  · apply Int.natAbs_dvd.mp
    rw [hm]
    exact Int.gcd_dvd_right a b

/-- Every common divisor divides the answer: greatestness up to sign. -/
def greatest_prop (a b r : Int) : Prop :=
  ∀ d : Int, d ∣ a → d ∣ b → d ∣ r

theorem greatest_thm (a b : Int) :
    greatest_prop a b (greatest_common_divisor a b) := by
  intro d ha hb
  apply Int.dvd_natAbs.mp
  rw [show (greatest_common_divisor a b).natAbs = Int.gcd a b from magnitude_thm a b]
  exact Int.dvd_coe_gcd ha hb

/-- Zero occurs exactly when both inputs are zero. -/
def zero_prop (a b r : Int) : Prop := r = 0 ↔ a = 0 ∧ b = 0

theorem zero_thm (a b : Int) :
    zero_prop a b (greatest_common_divisor a b) := by
  unfold zero_prop
  rw [← Int.natAbs_eq_zero,
    show (greatest_common_divisor a b).natAbs = Int.gcd a b from magnitude_thm a b]
  exact Int.gcd_eq_zero_iff

/-- Neither zero-input case normalizes away a negative sign. -/
def boundary_prop (a b r : Int) : Prop :=
  (b = 0 → r = a) ∧ (a = 0 → r = b)

theorem boundary_thm (a b : Int) :
    boundary_prop a b (greatest_common_divisor a b) := by
  constructor
  · intro hb
    subst b
    rw [greatest_common_divisor]
    simp
  · intro ha
    subst a
    rw [greatest_common_divisor]
    split_ifs with hb
    · exact hb.symm
    · simp [pythonMod, greatest_common_divisor]

/-- In the usual nonnegative input domain the answer is nonnegative. -/
def nonnegative_prop (a b r : Int) : Prop :=
  0 ≤ a → 0 ≤ b → 0 ≤ r

theorem nonnegative_thm (a b : Int) :
    nonnegative_prop a b (greatest_common_divisor a b) := by
  intro ha hb
  apply Int.sign_nonneg_iff.mp
  rw [show (greatest_common_divisor a b).sign =
      (if b = 0 then a.sign else b.sign) from sign_thm a b]
  split_ifs
  · exact Int.sign_nonneg_iff.mpr ha
  · exact Int.sign_nonneg_iff.mpr hb

/-- Complete postcondition: a greatest common divisor with Python's sign. -/
def Post_prop (a b r : Int) : Prop :=
  magnitude_prop a b r ∧ sign_prop a b r ∧ signed_value_prop a b r ∧
  common_divisor_prop a b r ∧ greatest_prop a b r ∧ zero_prop a b r ∧
  boundary_prop a b r ∧ nonnegative_prop a b r

/-! ## Property-based tests

Exhaustive signed samples include both axes, all four quadrants, and zero.
The universally quantified common-divisor candidate `d` is sampled separately;
this is an executable pointwise test of greatestness, not a substitute for the
unbounded theorem above. No input precondition is discarded: `Pre` is `True`.
-/

def testInts : List Int := (List.range 25).map (fun n => (n : Int) - 12)

def checkPairs (p : Int → Int → Int → Bool) : Bool :=
  testInts.all fun a => testInts.all fun b => p a b (greatest_common_divisor a b)

-- PBT for magnitude_prop.
example : checkPairs (fun a b r => decide (r.natAbs = Int.gcd a b)) = true := by
  native_decide
-- PBT for sign_prop.
example : checkPairs (fun a b r =>
    decide (r.sign = if b = 0 then a.sign else b.sign)) = true := by
  native_decide
-- PBT for signed_value_prop.
example : checkPairs (fun a b r =>
    decide (r = if b = 0 then a else b.sign * (Int.gcd a b : Int))) = true := by
  native_decide
-- PBT for common_divisor_prop.
example : checkPairs (fun a b r => decide (r ∣ a ∧ r ∣ b)) = true := by
  native_decide
-- PBT for greatest_prop: all 15,625 triples (a,b,d) in [-12,12]^3.
def greatestCheck (a b r : Int) : Bool :=
  testInts.all fun d => decide (d ∣ a → d ∣ b → d ∣ r)
example : checkPairs greatestCheck = true := by native_decide
-- PBT for zero_prop.
example : checkPairs (fun a b r => decide (r = 0 ↔ a = 0 ∧ b = 0)) = true := by
  native_decide
-- PBT for boundary_prop.
example : checkPairs (fun a b r =>
    decide ((b = 0 → r = a) ∧ (a = 0 → r = b))) = true := by native_decide
-- PBT for nonnegative_prop; the grid includes all 169 nonnegative pairs.
example : checkPairs (fun a b r => decide (0 ≤ a → 0 ≤ b → 0 ≤ r)) = true := by
  native_decide

/-- Executable postcondition, with the universal divisor tested pointwise. -/
def postCheck (a b r : Int) : Bool :=
  decide (r.natAbs = Int.gcd a b ∧
    r.sign = (if b = 0 then a.sign else b.sign) ∧
    r = (if b = 0 then a else b.sign * (Int.gcd a b : Int)) ∧
    (r ∣ a ∧ r ∣ b) ∧ (r = 0 ↔ a = 0 ∧ b = 0) ∧
    ((b = 0 → r = a) ∧ (a = 0 → r = b)) ∧
    (0 ≤ a → 0 ≤ b → 0 ≤ r)) && greatestCheck a b r

-- PBT for Post_prop, including sampled values of its universally quantified d.
example : checkPairs postCheck = true := by native_decide
#eval checkPairs postCheck

/-- Total correctness for every pair of Python integers. -/
theorem correctness (a b : Int) :
    Pre a b → Post_prop a b (greatest_common_divisor a b) := by
  intro _
  exact ⟨magnitude_thm a b, sign_thm a b, signed_value_thm a b,
    common_divisor_thm a b, greatest_thm a b, zero_thm a b,
    boundary_thm a b, nonnegative_thm a b⟩

/-! ## Imperative implementation

The loop has at most `b.natAbs` active iterations, since each active iteration
strictly decreases that natural-number measure. Once the divisor is zero,
remaining iterations are no-ops. The bound is proved sufficient below, not
assumed as a precondition or used as an approximation to the Python program.
-/

/-- Mutable simultaneous assignment, preserving the old first component. -/
def imperativeLoop (ticks : List Nat) (a b : Int) : Int × Int := Id.run do
  let mut x := a
  let mut y := b
  for _ in ticks do
    if y ≠ 0 then
      let oldX := x
      x := y
      y := pythonMod oldX y
  return (x, y)

/-- A total imperative realization of the Python while-loop. -/
def greatest_common_divisor_imperative (a b : Int) : Int := Id.run do
  let result := imperativeLoop (List.range b.natAbs) a b
  return result.1

-- Imperative tests: all doctests and public assertions, and signed regressions.
example : greatest_common_divisor_imperative 3 5 = 1 := by native_decide
example : greatest_common_divisor_imperative 25 15 = 5 := by native_decide
example : greatest_common_divisor_imperative 0 1 = 1 := by native_decide
example : greatest_common_divisor_imperative 2 0 = 2 := by native_decide
example : greatest_common_divisor_imperative 0 0 = 0 := by native_decide
example : greatest_common_divisor_imperative 3 7 = 1 := by native_decide
example : greatest_common_divisor_imperative 10 15 = 5 := by native_decide
example : greatest_common_divisor_imperative 49 14 = 7 := by native_decide
example : greatest_common_divisor_imperative 144 60 = 12 := by native_decide
example : greatest_common_divisor_imperative 10 (-15) = -5 := by native_decide
example : greatest_common_divisor_imperative (-10) 15 = 5 := by native_decide
example : greatest_common_divisor_imperative (-10) (-15) = -5 := by native_decide
example : greatest_common_divisor_imperative (-7) 0 = -7 := by native_decide
example : greatest_common_divisor_imperative 0 (-7) = -7 := by native_decide
#eval greatest_common_divisor_imperative 144 60
#eval greatest_common_divisor_imperative 10 (-15)
-- An additional bounded test compares both implementations on all 625 pairs.
example : checkPairs (fun a b r =>
    decide (r = greatest_common_divisor_imperative a b)) = true := by native_decide

lemma imperativeLoop_nil (a b : Int) : imperativeLoop [] a b = (a, b) := by
  rfl

lemma imperativeLoop_cons (tick : Nat) (ticks : List Nat) (a b : Int) :
    imperativeLoop (tick :: ticks) a b =
      if b = 0 then imperativeLoop ticks a b
      else imperativeLoop ticks b (pythonMod a b) := by
  by_cases hb : b = 0 <;> simp [imperativeLoop, hb]

/-- The bound is sufficient, and the loop finishes with divisor zero. -/
theorem imperativeLoop_correct (ticks : List Nat) (a b : Int)
    (h : b.natAbs ≤ ticks.length) :
    imperativeLoop ticks a b = (greatest_common_divisor a b, 0) := by
  induction ticks generalizing a b with
  | nil =>
      have hb : b = 0 := Int.natAbs_eq_zero.mp (by simpa using h)
      subst b
      rw [imperativeLoop_nil, greatest_common_divisor]
      simp
  | cons tick ticks ih =>
      rw [imperativeLoop_cons]
      by_cases hb : b = 0
      · rw [if_pos hb]
        exact ih a b (by simp [hb])
      · rw [if_neg hb]
        have hm := pythonMod_lt a b hb
        have hbound : (pythonMod a b).natAbs ≤ ticks.length := by
          simp only [List.length_cons] at h
          omega
        rw [ih b (pythonMod a b) hbound]
        conv_rhs => rw [greatest_common_divisor, dif_neg hb]

/-- The functional and mutable algorithms agree on every pair of integers. -/
theorem functional_eq_imperative (a b : Int) :
    greatest_common_divisor a b = greatest_common_divisor_imperative a b := by
  have h := imperativeLoop_correct (List.range b.natAbs) a b (by simp)
  change greatest_common_divisor a b = (imperativeLoop (List.range b.natAbs) a b).1
  rw [h]

end humaneval_13__gcd
end Agent
