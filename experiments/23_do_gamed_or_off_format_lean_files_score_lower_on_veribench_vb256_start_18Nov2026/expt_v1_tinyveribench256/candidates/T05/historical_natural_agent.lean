import Mathlib
namespace Agent

/-!
# `14_fractions_core` — rational numbers, ported from Python's `fractions.Fraction`

This file is a Lean 4 formalization of the core of Python's `fractions.Fraction`
class (constructor with normalization, sign convention, arithmetic and comparison).

* A `Fraction` is a pair of integers `num / den`.
* The constructor `normalize n d` mirrors Python's `Fraction.__new__`: it divides
  both arguments by `g = gcd(n, d)`, negating `g` first when `d < 0`, so that the
  result is in lowest terms with a positive denominator.
* `create? n d` models the full constructor including its failure modes:
  `d = none` is Python's default argument (`Fraction(n)`), and `d = some 0`
  raises `ZeroDivisionError`, modelled by `none`.
* `add`, `sub`, `mul`, `div`, `beq`, `blt` mirror `__add__`, `__sub__`,
  `__mul__`, `__truediv__`, `__eq__` and `__lt__`.

The specification is phrased through `toRat : Fraction → ℚ`, the rational number
denoted by a `Fraction`.
-/

namespace Fractions14

/-! ## Implementation (functional) -/

/-- A rational number, stored as a numerator/denominator pair, as in Python's
`Fraction` with its `_numerator` / `_denominator` slots. -/
structure Fraction where
  num : Int
  den : Int
deriving DecidableEq, Repr

/-- `g = math.gcd(n, d)`, negated when `d < 0` (Python: `if denominator < 0: g = -g`). -/
def gcdSigned (n d : Int) : Int :=
  if d < 0 then -(Int.gcd n d : Int) else (Int.gcd n d : Int)

/-- The normalizing constructor: `Fraction(n, d)` for `d ≠ 0`. -/
def normalize (n d : Int) : Fraction :=
  { num := n / gcdSigned n d, den := d / gcdSigned n d }

/-- `Fraction(n)` — the default-denominator branch of `__new__`. -/
def ofInt (n : Int) : Fraction := { num := n, den := 1 }

/-- The full Python constructor. `none` for the denominator is Python's default
argument; `some 0` raises `ZeroDivisionError`, which we model as `none`. -/
def create? (n : Int) (d : Option Int) : Option Fraction :=
  match d with
  | none => some (ofInt n)
  | some q => if q = 0 then none else some (normalize n q)

/-- The rational number denoted by a `Fraction`. -/
def toRat (f : Fraction) : ℚ := (f.num : ℚ) / (f.den : ℚ)

/-- Python's `__repr__`. -/
def repr' (f : Fraction) : String := s!"Fraction({f.num}, {f.den})"

/-- `__add__`. -/
def add (a b : Fraction) : Fraction :=
  normalize (a.num * b.den + a.den * b.num) (a.den * b.den)

/-- `__sub__`. -/
def sub (a b : Fraction) : Fraction :=
  normalize (a.num * b.den - a.den * b.num) (a.den * b.den)

/-- `__mul__`. -/
def mul (a b : Fraction) : Fraction :=
  normalize (a.num * b.num) (a.den * b.den)

/-- `__truediv__`. -/
def div (a b : Fraction) : Fraction :=
  normalize (a.num * b.den) (a.den * b.num)

/-- `__truediv__` including its `ZeroDivisionError` failure mode. -/
def div? (a b : Fraction) : Option Fraction :=
  if b.num = 0 then none else some (div a b)

/-- `__eq__`: Python compares the (normalized) numerator and denominator. -/
def beq (a b : Fraction) : Bool := a.num == b.num && a.den == b.den

/-- `__lt__`: cross-multiplication. -/
def blt (a b : Fraction) : Bool := a.num * b.den < a.den * b.num

/-! ## Unit tests (mirroring the Python `check` function) -/

-- 1. Normalization
example : normalize 8 6 = ⟨4, 3⟩ := by native_decide

-- 2. Sign convention
example : normalize 10 (-8) = ⟨-5, 4⟩ := by native_decide

-- 3. Defaults
example : create? 7 none = create? 7 (some 1) := by native_decide

-- 4. Error case: ZeroDivisionError
example : create? 1 (some 0) = none := by native_decide
example : div? (normalize 1 2) (normalize 0 5) = none := by native_decide

-- 5. Arithmetic
example : add (normalize 1 2) (normalize 1 3) = normalize 5 6 := by native_decide
example : mul (normalize 1 2) (normalize 2 3) = normalize 1 3 := by native_decide
example : div (normalize 1 2) (normalize 3 4) = normalize 2 3 := by native_decide
example : sub (normalize 3 4) (normalize 1 4) = normalize 1 2 := by native_decide

-- 6. Comparison
example : blt (normalize 1 2) (normalize 2 3) = true := by native_decide
example : blt (normalize 1 2) (normalize 1 2) = false := by native_decide
example : beq (normalize 1 2) (normalize 2 4) = true := by native_decide

#eval repr' (normalize 8 6)
#eval repr' (normalize 10 (-8))
#eval (add (normalize 1 2) (normalize 1 3)).num
#eval (add (normalize 1 2) (normalize 1 3)).den

/-! ## Pre-condition -/

/-- Python's `pre_create`: both arguments must be integers (guaranteed by typing
in Lean), and the constructor additionally requires a nonzero denominator in
order not to raise `ZeroDivisionError`. -/
def Pre (n : Int) (d : Option Int) : Prop :=
  match d with
  | none => True
  | some q => q ≠ 0

/-! ## Auxiliary lemmas -/

theorem ext' {a b : Fraction} (h1 : a.num = b.num) (h2 : a.den = b.den) : a = b := by
  cases a; cases b; simp_all

private theorem ediv_of_eq {x y z : Int} (hy : y ≠ 0) (h : x = y * z) : x / y = z := by
  subst h; exact Int.mul_ediv_cancel_left _ hy

private theorem gcd_ne_zero {n d : Int} (hd : d ≠ 0) : Int.gcd n d ≠ 0 := fun h =>
  hd (Int.gcd_eq_zero_iff.mp h).2

private theorem gcd_pos {n d : Int} (hd : d ≠ 0) : (0 : Int) < (Int.gcd n d : Int) := by
  have h : (Int.gcd n d : Int) ≠ 0 := Int.natCast_ne_zero.mpr (gcd_ne_zero (n := n) hd)
  exact lt_of_le_of_ne (Int.natCast_nonneg _) (Ne.symm h)

theorem gcdSigned_ne_zero {n d : Int} (hd : d ≠ 0) : gcdSigned n d ≠ 0 := by
  have h := gcd_pos (n := n) hd
  unfold gcdSigned
  split_ifs with hlt
  · omega
  · omega

/-- The signed gcd has the same sign as the denominator, which is what makes the
normalized denominator positive. -/
theorem mul_gcdSigned_pos {n d : Int} (hd : d ≠ 0) : 0 < d * gcdSigned n d := by
  have h := gcd_pos (n := n) hd
  unfold gcdSigned
  split_ifs with hlt
  · exact mul_pos_of_neg_of_neg hlt (by omega)
  · exact mul_pos (by omega) h

theorem gcdSigned_dvd_left (n d : Int) : gcdSigned n d ∣ n := by
  have h : ((Int.gcd n d : Int)) ∣ n := Int.gcd_dvd_left n d
  unfold gcdSigned
  split_ifs with hlt
  · exact (neg_dvd).mpr h
  · exact h

theorem gcdSigned_dvd_right (n d : Int) : gcdSigned n d ∣ d := by
  have h : ((Int.gcd n d : Int)) ∣ d := Int.gcd_dvd_right n d
  unfold gcdSigned
  split_ifs with hlt
  · exact (neg_dvd).mpr h
  · exact h

/-- Structural description of `normalize`: it divides both arguments by a common
nonzero factor whose sign agrees with the denominator's. -/
theorem normalize_eq {n d : Int} (hd : d ≠ 0) :
    ∃ g a b : Int, g ≠ 0 ∧ 0 < d * g ∧ n = g * a ∧ d = g * b ∧ normalize n d = ⟨a, b⟩ := by
  have hg := gcdSigned_ne_zero (n := n) hd
  obtain ⟨a, ha⟩ := gcdSigned_dvd_left n d
  obtain ⟨b, hb⟩ := gcdSigned_dvd_right n d
  refine ⟨gcdSigned n d, a, b, hg, mul_gcdSigned_pos hd, ha, hb, ?_⟩
  have h1 : n / gcdSigned n d = a := ediv_of_eq hg ha
  have h2 : d / gcdSigned n d = b := ediv_of_eq hg hb
  simp [normalize, h1, h2]

/-! ## Properties and theorems -/

/-- Property: the normalized denominator is strictly positive
(Python's sign convention: the sign lives in the numerator). -/
def den_pos_prop (n d : Int) : Prop := d ≠ 0 → 0 < (normalize n d).den

theorem den_pos_thm (n d : Int) : den_pos_prop n d := by
  intro hd
  obtain ⟨g, a, b, hg, hdg, ha, hb, he⟩ := normalize_eq (n := n) hd
  rw [he]
  subst hb
  by_contra hcon
  push_neg at hcon
  nlinarith [mul_self_nonneg g]

/-- Property: `normalize` produces a fraction in lowest terms
(this is what `g = math.gcd(...)` achieves). -/
def coprime_prop (n d : Int) : Prop :=
  d ≠ 0 → Int.gcd (normalize n d).num (normalize n d).den = 1

theorem coprime_thm (n d : Int) : coprime_prop n d := by
  intro hd
  have hpos : 0 < Int.gcd n d := Nat.pos_of_ne_zero (gcd_ne_zero (n := n) hd)
  have key := Int.gcd_div_gcd_div_gcd (i := n) (j := d) hpos
  simp only [normalize, gcdSigned]
  split_ifs with hlt
  · simpa [Int.ediv_neg, Int.neg_gcd, Int.gcd_neg] using key
  · simpa using key

/-- Property: `normalize n d` denotes the rational `n / d` — stated without
division, as the cross-multiplication identity. -/
def value_prop (n d : Int) : Prop :=
  d ≠ 0 → (normalize n d).num * d = n * (normalize n d).den

theorem value_thm (n d : Int) : value_prop n d := by
  intro hd
  obtain ⟨g, a, b, hg, hdg, ha, hb, he⟩ := normalize_eq (n := n) hd
  rw [he, ha, hb]
  ring

/-- The value of `normalize n d` as a rational number. -/
theorem toRat_normalize {n d : Int} (hd : d ≠ 0) :
    toRat (normalize n d) = (n : ℚ) / (d : ℚ) := by
  obtain ⟨g, a, b, hg, hdg, ha, hb, he⟩ := normalize_eq (n := n) hd
  have hbne : b ≠ 0 := by
    rintro rfl; rw [hb] at hdg; simp at hdg
  have hgQ : (g : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hg
  have hbQ : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hbne
  rw [toRat, he, ha, hb]
  push_cast
  field_simp
  ring

/-- `normalize` is idempotent-ish: an already normalized fraction is a fixed point. -/
def Normalized (f : Fraction) : Prop := 0 < f.den ∧ Int.gcd f.num f.den = 1

theorem normalize_normalized {n d : Int} (hd : d ≠ 0) : Normalized (normalize n d) :=
  ⟨den_pos_thm n d hd, coprime_thm n d hd⟩

/-- Property: Python's structural `__eq__` on normalized fractions decides
equality of the rational values. -/
def eq_prop (a b : Fraction) : Prop :=
  Normalized a → Normalized b → (beq a b = true ↔ toRat a = toRat b)

theorem eq_thm (a b : Fraction) : eq_prop a b := by
  intro ha hb
  have hda0 : a.den ≠ 0 := by have := ha.1; omega
  have hdb0 : b.den ≠ 0 := by have := hb.1; omega
  have hda : (a.den : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hda0
  have hdb : (b.den : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hdb0
  constructor
  · intro h
    simp only [beq, Bool.and_eq_true, beq_iff_eq] at h
    rw [toRat, toRat, h.1, h.2]
  · intro h
    rw [toRat, toRat, div_eq_div_iff hda hdb] at h
    have hcross : a.num * b.den = b.num * a.den := by exact_mod_cast h
    have hca : IsCoprime a.den a.num := (Int.isCoprime_iff_gcd_eq_one.mpr ha.2).symm
    have hcb : IsCoprime b.den b.num := (Int.isCoprime_iff_gcd_eq_one.mpr hb.2).symm
    have h1 : a.den ∣ b.den := hca.dvd_of_dvd_mul_left ⟨b.num, by rw [hcross]; ring⟩
    have h2 : b.den ∣ a.den := hcb.dvd_of_dvd_mul_left ⟨a.num, by rw [← hcross]; ring⟩
    have hden : a.den = b.den := Int.dvd_antisymm (le_of_lt ha.1) (le_of_lt hb.1) h1 h2
    have hnum : a.num = b.num := by
      apply mul_right_cancel₀ hda0
      rw [← hden] at hcross
      exact hcross
    simp [beq, hnum, hden]

/-- Property: `__lt__` computes the order on the rational values. -/
def lt_prop (a b : Fraction) : Prop :=
  0 < a.den → 0 < b.den → (blt a b = true ↔ toRat a < toRat b)

theorem lt_thm (a b : Fraction) : lt_prop a b := by
  intro ha hb
  have ha' : (0 : ℚ) < (a.den : ℚ) := by exact_mod_cast ha
  have hb' : (0 : ℚ) < (b.den : ℚ) := by exact_mod_cast hb
  rw [toRat, toRat, div_lt_div_iff₀ ha' hb']
  simp only [blt, decide_eq_true_eq]
  rw [show a.den * b.num = b.num * a.den from mul_comm _ _]
  constructor <;> intro h <;> exact_mod_cast h

/-- Property: `__add__` implements addition of rationals. -/
def add_prop (a b : Fraction) : Prop :=
  a.den ≠ 0 → b.den ≠ 0 → toRat (add a b) = toRat a + toRat b

theorem add_thm (a b : Fraction) : add_prop a b := by
  intro ha hb
  have h : a.den * b.den ≠ 0 := mul_ne_zero ha hb
  have haQ : (a.den : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hbQ : (b.den : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb
  rw [add, toRat_normalize h, toRat, toRat]
  push_cast
  field_simp
  ring

/-- Property: `__sub__` implements subtraction of rationals. -/
def sub_prop (a b : Fraction) : Prop :=
  a.den ≠ 0 → b.den ≠ 0 → toRat (sub a b) = toRat a - toRat b

theorem sub_thm (a b : Fraction) : sub_prop a b := by
  intro ha hb
  have h : a.den * b.den ≠ 0 := mul_ne_zero ha hb
  have haQ : (a.den : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hbQ : (b.den : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb
  rw [sub, toRat_normalize h, toRat, toRat]
  push_cast
  field_simp

/-- Property: `__mul__` implements multiplication of rationals. -/
def mul_prop (a b : Fraction) : Prop :=
  a.den ≠ 0 → b.den ≠ 0 → toRat (mul a b) = toRat a * toRat b

theorem mul_thm (a b : Fraction) : mul_prop a b := by
  intro ha hb
  have h : a.den * b.den ≠ 0 := mul_ne_zero ha hb
  have haQ : (a.den : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hbQ : (b.den : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb
  rw [mul, toRat_normalize h, toRat, toRat]
  push_cast
  field_simp

/-- Property: `__truediv__` implements division of rationals; it is defined
exactly when the divisor's numerator is nonzero. -/
def div_prop (a b : Fraction) : Prop :=
  a.den ≠ 0 → b.den ≠ 0 → b.num ≠ 0 →
    div? a b = some (div a b) ∧ toRat (div a b) = toRat a / toRat b

theorem div_thm (a b : Fraction) : div_prop a b := by
  intro ha hb hbn
  refine ⟨by simp [div?, hbn], ?_⟩
  have h : a.den * b.num ≠ 0 := mul_ne_zero ha hbn
  have haQ : (a.den : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hbQ : (b.den : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have hbnQ : (b.num : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hbn
  rw [div, toRat_normalize h, toRat, toRat]
  push_cast
  field_simp

/-- Property: dividing by zero is the `ZeroDivisionError` case. -/
def div_zero_prop (a b : Fraction) : Prop := b.num = 0 → div? a b = none

theorem div_zero_thm (a b : Fraction) : div_zero_prop a b := by
  intro h; simp [div?, h]

/-- Property: the constructor fails exactly on a zero denominator, i.e. exactly
when the pre-condition fails. -/
def create_fails_prop (n : Int) (d : Option Int) : Prop :=
  create? n d = none ↔ ¬ Pre n d

theorem create_fails_thm (n : Int) (d : Option Int) : create_fails_prop n d := by
  cases d with
  | none => simp [create_fails_prop, create?, Pre]
  | some q =>
      by_cases h : q = 0 <;> simp [create_fails_prop, create?, Pre, h]

/-- Property: the default denominator is `1` (`Fraction(n)` = `Fraction(n, 1)`). -/
def default_prop (n : Int) : Prop :=
  create? n none = some ⟨n, 1⟩ ∧ create? n none = create? n (some 1)

theorem default_thm (n : Int) : default_prop n := by
  refine ⟨rfl, ?_⟩
  have h : normalize n 1 = ⟨n, 1⟩ := by
    have : gcdSigned n 1 = 1 := by simp [gcdSigned]
    simp [normalize, this]
  simp [create?, ofInt, h]

/-! ## Post-condition -/

/-- The post-condition of the constructor: it succeeds, the result is in lowest
terms with a positive denominator, and it denotes the intended rational value. -/
def Post_prop (n : Int) (d : Option Int) : Prop :=
  ∃ f : Fraction,
    create? n d = some f ∧
    0 < f.den ∧
    Int.gcd f.num f.den = 1 ∧
    toRat f = (match d with | none => (n : ℚ) | some q => (n : ℚ) / (q : ℚ))

/-- Correctness of the constructor: `Pre → Post`. -/
theorem correctness (n : Int) (d : Option Int) (h : Pre n d) : Post_prop n d := by
  cases d with
  | none =>
      refine ⟨⟨n, 1⟩, rfl, by norm_num, by simp, ?_⟩
      simp [toRat]
  | some q =>
      have hq : q ≠ 0 := h
      refine ⟨normalize n q, by simp [create?, hq], den_pos_thm n q hq,
        coprime_thm n q hq, ?_⟩
      simpa using toRat_normalize (n := n) hq

/-! ## Imperative implementation (`Id.run do` with mutable state) -/

/-- Imperative rendering of Python's `__new__` body for the two-argument case. -/
def normalizeImp (n d : Int) : Fraction := Id.run do
  let mut g : Int := (Int.gcd n d : Int)
  if d < 0 then
    g := -g
  let num : Int := n / g
  let den : Int := d / g
  return { num := num, den := den }

/-- Imperative rendering of the full constructor, including both early returns. -/
def createImp? (n : Int) (d : Option Int) : Option Fraction := Id.run do
  match d with
  | none => return some { num := n, den := 1 }
  | some q =>
      if q = 0 then
        return none
      else
        return some (normalizeImp n q)

def addImp (a b : Fraction) : Fraction := Id.run do
  let num : Int := a.num * b.den + a.den * b.num
  let den : Int := a.den * b.den
  return normalizeImp num den

def subImp (a b : Fraction) : Fraction := Id.run do
  let num : Int := a.num * b.den - a.den * b.num
  let den : Int := a.den * b.den
  return normalizeImp num den

def mulImp (a b : Fraction) : Fraction := Id.run do
  let num : Int := a.num * b.num
  let den : Int := a.den * b.den
  return normalizeImp num den

def divImp (a b : Fraction) : Fraction := Id.run do
  let num : Int := a.num * b.den
  let den : Int := a.den * b.num
  return normalizeImp num den

def bltImp (a b : Fraction) : Bool := Id.run do
  let l : Int := a.num * b.den
  let r : Int := a.den * b.num
  return l < r

/-! ## Imperative tests -/

example : normalizeImp 8 6 = ⟨4, 3⟩ := by native_decide
example : normalizeImp 10 (-8) = ⟨-5, 4⟩ := by native_decide
example : createImp? 7 none = createImp? 7 (some 1) := by native_decide
example : createImp? 1 (some 0) = none := by native_decide
example : addImp (normalizeImp 1 2) (normalizeImp 1 3) = normalizeImp 5 6 := by native_decide
example : mulImp (normalizeImp 1 2) (normalizeImp 2 3) = normalizeImp 1 3 := by native_decide
example : divImp (normalizeImp 1 2) (normalizeImp 3 4) = normalizeImp 2 3 := by native_decide
example : subImp (normalizeImp 3 4) (normalizeImp 1 4) = normalizeImp 1 2 := by native_decide
example : bltImp (normalizeImp 1 2) (normalizeImp 2 3) = true := by native_decide

#eval repr' (normalizeImp 10 (-8))

/-! ## Equivalence of the functional and imperative implementations -/

theorem normalizeImp_eq (n d : Int) : normalizeImp n d = normalize n d := by
  simp only [normalizeImp, normalize, gcdSigned, Id.run]
  split_ifs <;> rfl

theorem createImp?_eq (n : Int) (d : Option Int) : createImp? n d = create? n d := by
  cases d with
  | none => rfl
  | some q =>
      simp only [createImp?, create?, Id.run, normalizeImp_eq]
      split_ifs <;> rfl

theorem addImp_eq (a b : Fraction) : addImp a b = add a b := by
  simp only [addImp, add, Id.run, normalizeImp_eq]
  rfl

theorem subImp_eq (a b : Fraction) : subImp a b = sub a b := by
  simp only [subImp, sub, Id.run, normalizeImp_eq]
  rfl

theorem mulImp_eq (a b : Fraction) : mulImp a b = mul a b := by
  simp only [mulImp, mul, Id.run, normalizeImp_eq]
  rfl

theorem divImp_eq (a b : Fraction) : divImp a b = div a b := by
  simp only [divImp, div, Id.run, normalizeImp_eq]
  rfl

theorem bltImp_eq (a b : Fraction) : bltImp a b = blt a b := rfl

/-- The functional and imperative implementations agree everywhere. -/
theorem equivalence :
    (∀ n d : Int, normalizeImp n d = normalize n d) ∧
    (∀ (n : Int) (d : Option Int), createImp? n d = create? n d) ∧
    (∀ a b : Fraction, addImp a b = add a b) ∧
    (∀ a b : Fraction, subImp a b = sub a b) ∧
    (∀ a b : Fraction, mulImp a b = mul a b) ∧
    (∀ a b : Fraction, divImp a b = div a b) ∧
    (∀ a b : Fraction, bltImp a b = blt a b) :=
  ⟨normalizeImp_eq, createImp?_eq, addImp_eq, subImp_eq, mulImp_eq, divImp_eq, bltImp_eq⟩

end Fractions14
end Agent
