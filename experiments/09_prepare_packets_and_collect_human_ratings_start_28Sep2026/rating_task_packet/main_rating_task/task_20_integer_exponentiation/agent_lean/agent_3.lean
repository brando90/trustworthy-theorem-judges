import Mathlib

/-!
# 19_MyPower

Lean 4 formalization of the Python `power` program: base raised to a natural exponent.

Python semantics preserved here:

- `power(n, 0) = 1` for every natural `n`, and `power(0, 0) = 1` by convention
- `power(0, n) = 0` for every `n > 0`
- both arguments must be natural numbers (non-negative integers); otherwise the
  program raises `ValueError`
- on the success path the value is computed by repeated multiplication
  (`result = 1; repeat exponent times: result *= base`), which is unbounded
  integer arithmetic, matching Python `int`

Model:

- inputs are `Int` (unbounded, like Python `int`); being an `int` is enforced by the type
- `Pre` is non-negativity of both arguments
- `ValueError` is `Except.error` carrying the Python error text
- `prog` is the functional implementation; `progImp` is the imperative loop
-/

namespace «19_MyPower»

/-- Message matching Python's `ValueError` text. -/
def errorMsg (base exponent : Int) : String :=
  s!"Require base,exponent ∈ ℕ (got base={base}, exponent={exponent})"

/-- Boolean precondition: both inputs are non-negative integers. Mirrors Python `pre`. -/
def pre (base exponent : Int) : Bool :=
  decide (0 ≤ base) && decide (0 ≤ exponent)

/-- `base^exponent` by recursion, i.e. repeated multiplication.

`myPower base 0 = 1` for every `base`, including `myPower 0 0 = 1`. -/
def myPower (base : Nat) : Nat → Nat
  | 0 => 1
  | e + 1 => myPower base e * base

/-- Functional translation of Python `prog`.

Returns `Except.ok (base^exponent)` when both arguments are natural numbers,
and `Except.error` (the `ValueError`) otherwise. -/
def prog (base exponent : Int) : Except String Int :=
  if pre base exponent then
    .ok (↑(myPower base.toNat exponent.toNat))
  else
    .error (errorMsg base exponent)

instance : DecidableEq (Except String Int) := fun a b =>
  match a, b with
  | .error x, .error y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (fun he => by cases he; exact h rfl)
  | .ok x, .ok y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (fun he => by cases he; exact h rfl)
  | .error _, .ok _ => isFalse (fun h => by cases h)
  | .ok _, .error _ => isFalse (fun h => by cases h)

/-! ## Unit tests -/

example : prog 2 3 = .ok 8 := by native_decide
example : prog 0 0 = .ok 1 := by native_decide
example : prog 0 5 = .ok 0 := by native_decide
example : prog 7 0 = .ok 1 := by native_decide
example : prog 1 8 = .ok 1 := by native_decide
example : prog 3 4 = .ok 81 := by native_decide
example : prog 10 3 = .ok 1000 := by native_decide
example : prog 2 10 = .ok 1024 := by native_decide
example : prog (-1) 2 = .error (errorMsg (-1) 2) := by native_decide
example : prog 2 (-1) = .error (errorMsg 2 (-1)) := by native_decide
example : prog (-3) (-1) = .error (errorMsg (-3) (-1)) := by native_decide
example : prog (-4) 0 = .error (errorMsg (-4) 0) := by native_decide
example : myPower 2 3 = 8 := by native_decide
example : myPower 0 0 = 1 := by native_decide
example : myPower 0 4 = 0 := by native_decide

#eval prog 2 3
#eval prog 0 0
#eval prog 0 5
#eval prog (-1) 2
#eval prog 2 (-1)
#eval myPower 2 10

/-! ## Precondition -/

/-- Both arguments are natural numbers: non-negative integers. -/
def Pre (base exponent : Int) : Prop :=
  0 ≤ base ∧ 0 ≤ exponent

/-! ## Properties and theorems -/

/-- The Boolean `pre` agrees with the proposition `Pre`. -/
def pre_iff_prop (base exponent : Int) : Prop :=
  pre base exponent = true ↔ Pre base exponent

theorem pre_iff_thm (base exponent : Int) : pre_iff_prop base exponent := by
  unfold pre_iff_prop pre Pre
  simp [Bool.and_eq_true]

/-- Repeated multiplication agrees with mathematical exponentiation. -/
def pow_eq_prop (base exponent : Nat) : Prop :=
  myPower base exponent = base ^ exponent

theorem pow_eq_thm (base exponent : Nat) : pow_eq_prop base exponent := by
  unfold pow_eq_prop
  induction exponent with
  | zero => rfl
  | succ e ih =>
    simp only [myPower, Nat.pow_succ, ih]

/-- `power(n, 0) = 1` for every natural `n`. -/
def zero_exp_prop (base : Nat) : Prop :=
  myPower base 0 = 1

theorem zero_exp_thm (base : Nat) : zero_exp_prop base := by
  unfold zero_exp_prop
  rfl

/-- `power(0, n) = 0` for every `n > 0`. -/
def zero_base_prop (exponent : Nat) : Prop :=
  0 < exponent → myPower 0 exponent = 0

theorem zero_base_thm (exponent : Nat) : zero_base_prop exponent := by
  unfold zero_base_prop
  intro h
  rw [pow_eq_thm, Nat.zero_pow h]

/-- `power(0, 0) = 1` by convention. -/
def zero_zero_prop : Prop :=
  myPower 0 0 = 1

theorem zero_zero_thm : zero_zero_prop := by
  unfold zero_zero_prop
  rfl

/-- One iteration of `result *= base`. -/
def succ_prop (base exponent : Nat) : Prop :=
  myPower base (exponent + 1) = myPower base exponent * base

theorem succ_thm (base exponent : Nat) : succ_prop base exponent := by
  unfold succ_prop
  rfl

/-- Exponent `1` returns the base. -/
def one_exp_prop (base : Nat) : Prop :=
  myPower base 1 = base

theorem one_exp_thm (base : Nat) : one_exp_prop base := by
  unfold one_exp_prop
  simp [myPower]

/-- `1` to any power is `1`. -/
def one_base_prop (exponent : Nat) : Prop :=
  myPower 1 exponent = 1

theorem one_base_thm (exponent : Nat) : one_base_prop exponent := by
  unfold one_base_prop
  rw [pow_eq_thm, Nat.one_pow]

/-- Exponents add: `b^(m+n) = b^m * b^n`, the loop split into two segments. -/
def add_exp_prop (base m n : Nat) : Prop :=
  myPower base (m + n) = myPower base m * myPower base n

theorem add_exp_thm (base m n : Nat) : add_exp_prop base m n := by
  unfold add_exp_prop
  rw [pow_eq_thm, pow_eq_thm, pow_eq_thm, Nat.pow_add]

/-- `(b^m)^n = b^(m*n)`. -/
def pow_mul_prop (base m n : Nat) : Prop :=
  myPower (myPower base m) n = myPower base (m * n)

theorem pow_mul_thm (base m n : Nat) : pow_mul_prop base m n := by
  unfold pow_mul_prop
  calc
    myPower (myPower base m) n = (myPower base m) ^ n := pow_eq_thm _ _
    _ = (base ^ m) ^ n := by rw [pow_eq_thm]
    _ = base ^ (m * n) := by rw [← Nat.pow_mul]
    _ = myPower base (m * n) := by rw [← pow_eq_thm]

/-- `(a*b)^n = a^n * b^n`. -/
def mul_base_prop (a b n : Nat) : Prop :=
  myPower (a * b) n = myPower a n * myPower b n

theorem mul_base_thm (a b n : Nat) : mul_base_prop a b n := by
  unfold mul_base_prop
  calc
    myPower (a * b) n = (a * b) ^ n := pow_eq_thm _ _
    _ = a ^ n * b ^ n := Nat.mul_pow a b n
    _ = myPower a n * b ^ n := by rw [← pow_eq_thm]
    _ = myPower a n * myPower b n := by rw [← pow_eq_thm]

/-- A positive base yields a positive power (including exponent `0`, which is `1`). -/
def pos_prop (base exponent : Nat) : Prop :=
  0 < base → 0 < myPower base exponent

theorem pos_thm (base exponent : Nat) : pos_prop base exponent := by
  unfold pos_prop
  intro h
  rw [pow_eq_thm]
  exact Nat.pow_pos h

/-- Exponentiation is monotone in the base. -/
def mono_base_prop (a b exponent : Nat) : Prop :=
  a ≤ b → myPower a exponent ≤ myPower b exponent

theorem mono_base_thm (a b exponent : Nat) : mono_base_prop a b exponent := by
  unfold mono_base_prop
  intro h
  rw [pow_eq_thm, pow_eq_thm]
  exact Nat.pow_le_pow_left h exponent

/-- For a positive base, exponentiation is monotone in the exponent. -/
def mono_exp_prop (base e1 e2 : Nat) : Prop :=
  0 < base → e1 ≤ e2 → myPower base e1 ≤ myPower base e2

theorem mono_exp_thm (base e1 e2 : Nat) : mono_exp_prop base e1 e2 := by
  unfold mono_exp_prop
  intro hb hle
  rw [pow_eq_thm, pow_eq_thm]
  exact Nat.pow_le_pow_right hb hle

/-- Folding `acc ↦ acc * base` over `range exponent`, from `1`, is the Python loop. -/
def iter_prop (base exponent : Nat) : Prop :=
  (List.range exponent).foldl (fun acc (_ : Nat) => acc * base) 1 = myPower base exponent

private theorem foldl_mul_nat (base acc n : Nat) :
    (List.range n).foldl (fun r (_ : Nat) => r * base) acc = acc * base ^ n := by
  induction n generalizing acc with
  | zero => simp [List.range_zero]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp [Nat.pow_succ, Nat.mul_assoc]

theorem iter_thm (base exponent : Nat) : iter_prop base exponent := by
  unfold iter_prop
  rw [foldl_mul_nat, Nat.one_mul, pow_eq_thm]

/-- On `Pre`, `prog` returns the repeated-multiplication power. -/
def prog_ok_prop (base exponent : Int) : Prop :=
  Pre base exponent →
    prog base exponent = .ok (↑(myPower base.toNat exponent.toNat))

theorem prog_ok_thm (base exponent : Int) : prog_ok_prop base exponent := by
  unfold prog_ok_prop
  intro hPre
  have hiff := pre_iff_thm base exponent
  unfold pre_iff_prop at hiff
  have hp : pre base exponent = true := hiff.mpr hPre
  simp [prog, hp]

private theorem myPower_cast_eq_int_pow (base exponent : Int) (hb : 0 ≤ base) :
    ((myPower base.toNat exponent.toNat : Nat) : Int) = base ^ exponent.toNat := by
  rw [pow_eq_thm, Int.natCast_pow, Int.toNat_of_nonneg hb]

/-- On `Pre`, `prog` returns the mathematical integer power `base ^ exponent`. -/
def prog_math_prop (base exponent : Int) : Prop :=
  Pre base exponent →
    prog base exponent = .ok (base ^ exponent.toNat)

theorem prog_math_thm (base exponent : Int) : prog_math_prop base exponent := by
  unfold prog_math_prop
  intro hPre
  have hok := prog_ok_thm base exponent hPre
  rw [hok]
  exact congrArg Except.ok (myPower_cast_eq_int_pow base exponent hPre.1)

/-- Python edge: `power(n, 0) = 1` for every natural `n`. -/
def prog_zero_exp_prop (base : Int) : Prop :=
  0 ≤ base → prog base 0 = .ok 1

theorem prog_zero_exp_thm (base : Int) : prog_zero_exp_prop base := by
  unfold prog_zero_exp_prop
  intro hb
  have hok := prog_ok_thm base 0 ⟨hb, Int.le_refl 0⟩
  simpa [myPower] using hok

private theorem toNat_pos_of_pos {n : Int} (h : 0 < n) : 0 < n.toNat := by
  apply Nat.pos_of_ne_zero
  intro hz
  exact absurd (lt_of_lt_of_le h (Int.toNat_eq_zero.mp hz)) (lt_irrefl (0 : Int))

/-- Python edge: `power(0, n) = 0` for `n > 0`. -/
def prog_zero_base_prop (exponent : Int) : Prop :=
  0 < exponent → prog 0 exponent = .ok 0

theorem prog_zero_base_thm (exponent : Int) : prog_zero_base_prop exponent := by
  unfold prog_zero_base_prop
  intro he
  have hPre : Pre 0 exponent := ⟨Int.le_refl 0, le_of_lt he⟩
  have hok := prog_ok_thm 0 exponent hPre
  have htn : 0 < exponent.toNat := toNat_pos_of_pos he
  rw [hok, Int.toNat_zero, pow_eq_thm, Nat.zero_pow htn]
  rfl

/-- Python edge: `power(0, 0) = 1`. -/
def prog_zero_zero_prop : Prop :=
  prog 0 0 = .ok 1

theorem prog_zero_zero_thm : prog_zero_zero_prop := by
  unfold prog_zero_zero_prop
  simpa using prog_zero_exp_thm 0 (Int.le_refl 0)

/-- Violating `Pre` raises `ValueError`. -/
def valueError_prop (base exponent : Int) : Prop :=
  ¬ Pre base exponent →
    prog base exponent = .error (errorMsg base exponent)

theorem valueError_thm (base exponent : Int) : valueError_prop base exponent := by
  unfold valueError_prop
  intro hNot
  have hiff := pre_iff_thm base exponent
  unfold pre_iff_prop at hiff
  cases hp : pre base exponent with
  | false => simp [prog, hp]
  | true => exact absurd (hiff.mp hp) hNot

/-- A negative base is rejected, as in the Python tests. -/
def neg_base_prop (base exponent : Int) : Prop :=
  base < 0 → prog base exponent = .error (errorMsg base exponent)

theorem neg_base_thm (base exponent : Int) : neg_base_prop base exponent := by
  unfold neg_base_prop
  intro hb
  apply valueError_thm
  intro hPre
  exact absurd hPre.1 (not_le_of_gt hb)

/-- A negative exponent is rejected, as in the Python tests. -/
def neg_exp_prop (base exponent : Int) : Prop :=
  exponent < 0 → prog base exponent = .error (errorMsg base exponent)

theorem neg_exp_thm (base exponent : Int) : neg_exp_prop base exponent := by
  unfold neg_exp_prop
  intro he
  apply valueError_thm
  intro hPre
  exact absurd hPre.2 (not_le_of_gt he)

/-- The two negative inputs from the Python `check` harness raise `ValueError`. -/
def bad_inputs_prop : Prop :=
  prog (-1) 2 = .error (errorMsg (-1) 2) ∧
  prog 2 (-1) = .error (errorMsg 2 (-1))

theorem bad_inputs_thm : bad_inputs_prop := by
  unfold bad_inputs_prop
  refine ⟨?_, ?_⟩
  · exact neg_base_thm (-1) 2 (by decide)
  · exact neg_exp_thm 2 (-1) (by decide)

/-- A successful call returns a non-negative integer (a natural number). -/
def result_nonneg_prop (base exponent : Int) : Prop :=
  Pre base exponent → ∃ n : Nat, prog base exponent = .ok (↑n)

theorem result_nonneg_thm (base exponent : Int) : result_nonneg_prop base exponent := by
  unfold result_nonneg_prop
  intro hPre
  exact ⟨myPower base.toNat exponent.toNat, prog_ok_thm base exponent hPre⟩

/-! ## Post-condition -/

/-- Success post-condition, required whenever `Pre` holds.

The result is the repeated-multiplication power and the integer power
`base ^ exponent`, and the three documented edge cases hold. -/
def Post_prop (base exponent : Int) : Prop :=
  prog base exponent = .ok (↑(myPower base.toNat exponent.toNat)) ∧
  prog base exponent = .ok (base ^ exponent.toNat) ∧
  (exponent = 0 → prog base exponent = .ok 1) ∧
  (base = 0 ∧ exponent = 0 → prog base exponent = .ok 1) ∧
  (base = 0 ∧ 0 < exponent → prog base exponent = .ok 0)

/-! ## Property-based tests

Random checks use Plausible on admissible inputs (naturals, or explicitly negative
integers) so every sample meets the guard. Bounded checks exhaust a small grid,
including the negative inputs that raise `ValueError`.
-/

def pbtCfg : Plausible.Configuration where
  numInst := 25
  maxSize := 10
  quiet := true

/-- Integers used by the exhaustive grid, covering negatives and the edges `0` and `0^0`. -/
def pbtInts : List Int := [0, 1, 2, 3, 4, 5, 6, 7, -1, -2, -3, -4]

-- PBT for pow_eq_prop
#eval Plausible.Testable.check
  (∀ base exponent : Nat, myPower base exponent = base ^ exponent) pbtCfg

example : (List.range 20).all (fun b =>
    (List.range 8).all (fun e => myPower b e == b ^ e)) = true := by native_decide

-- PBT for zero_exp_prop
#eval Plausible.Testable.check (∀ base : Nat, myPower base 0 = 1) pbtCfg

example : (List.range 40).all (fun b => myPower b 0 == 1) = true := by native_decide

-- PBT for zero_base_prop
#eval Plausible.Testable.check (∀ exponent : Nat, myPower 0 (exponent + 1) = 0) pbtCfg

example : (List.range 40).all (fun e => e == 0 || myPower 0 e == 0) = true := by native_decide

-- PBT for zero_zero_prop (single conventional point)
example : myPower 0 0 == 1 := by native_decide

-- PBT for succ_prop
#eval Plausible.Testable.check
  (∀ base exponent : Nat, myPower base (exponent + 1) = myPower base exponent * base) pbtCfg

example : (List.range 15).all (fun b =>
    (List.range 8).all (fun e => myPower b (e + 1) == myPower b e * b)) = true := by native_decide

-- PBT for one_exp_prop
#eval Plausible.Testable.check (∀ base : Nat, myPower base 1 = base) pbtCfg

example : (List.range 40).all (fun b => myPower b 1 == b) = true := by native_decide

-- PBT for one_base_prop
#eval Plausible.Testable.check (∀ exponent : Nat, myPower 1 exponent = 1) pbtCfg

example : (List.range 40).all (fun e => myPower 1 e == 1) = true := by native_decide

-- PBT for add_exp_prop
#eval Plausible.Testable.check
  (∀ base m n : Nat, myPower base (m + n) = myPower base m * myPower base n) pbtCfg

example : (List.range 8).all (fun b =>
    (List.range 6).all (fun m =>
      (List.range 6).all (fun n => myPower b (m + n) == myPower b m * myPower b n))) = true := by
  native_decide

-- PBT for pow_mul_prop
#eval Plausible.Testable.check
  (∀ base m n : Nat, myPower (myPower base m) n = myPower base (m * n)) pbtCfg

example : (List.range 6).all (fun b =>
    (List.range 4).all (fun m =>
      (List.range 4).all (fun n => myPower (myPower b m) n == myPower b (m * n)))) = true := by
  native_decide

-- PBT for mul_base_prop
#eval Plausible.Testable.check
  (∀ a b n : Nat, myPower (a * b) n = myPower a n * myPower b n) pbtCfg

example : (List.range 6).all (fun a =>
    (List.range 6).all (fun b =>
      (List.range 5).all (fun n => myPower (a * b) n == myPower a n * myPower b n))) = true := by
  native_decide

-- PBT for pos_prop
#eval Plausible.Testable.check (∀ base exponent : Nat, 0 < myPower (base + 1) exponent) pbtCfg

example : (List.range 12).all (fun b =>
    (List.range 8).all (fun e => 0 < myPower (b + 1) e)) = true := by native_decide

-- PBT for mono_base_prop
#eval Plausible.Testable.check
  (∀ a k exponent : Nat, myPower a exponent ≤ myPower (a + k) exponent) pbtCfg

example : (List.range 8).all (fun a =>
    (List.range 6).all (fun k =>
      (List.range 5).all (fun e => myPower a e ≤ myPower (a + k) e))) = true := by native_decide

-- PBT for mono_exp_prop
#eval Plausible.Testable.check
  (∀ base e1 k : Nat, myPower (base + 1) e1 ≤ myPower (base + 1) (e1 + k)) pbtCfg

example : (List.range 6).all (fun b =>
    (List.range 5).all (fun e1 =>
      (List.range 5).all (fun k => myPower (b + 1) e1 ≤ myPower (b + 1) (e1 + k)))) = true := by
  native_decide

-- PBT for iter_prop
#eval Plausible.Testable.check
  (∀ base exponent : Nat,
    (List.range exponent).foldl (fun acc (_ : Nat) => acc * base) 1 = myPower base exponent)
  pbtCfg

example : (List.range 12).all (fun b =>
    (List.range 8).all (fun e =>
      (List.range e).foldl (fun acc (_ : Nat) => acc * b) 1 == myPower b e)) = true := by
  native_decide

-- PBT for pre_iff_prop
#eval Plausible.Testable.check
  (∀ base exponent : Int, pre base exponent = true ↔ 0 ≤ base ∧ 0 ≤ exponent) pbtCfg

example : pbtInts.all (fun b =>
    pbtInts.all (fun e => pre b e == decide (0 ≤ b ∧ 0 ≤ e))) = true := by native_decide

-- PBT for prog_ok_prop, on the natural numbers (the `Pre` domain)
#eval Plausible.Testable.check
  (∀ base exponent : Nat,
    prog (base : Int) (exponent : Int) = .ok (↑(myPower base exponent))) pbtCfg

example : (List.range 12).all (fun b =>
    (List.range 8).all (fun e =>
      prog (b : Int) (e : Int) == .ok (↑(myPower b e)))) = true := by native_decide

-- PBT for prog_math_prop
#eval Plausible.Testable.check
  (∀ base exponent : Nat,
    prog (base : Int) (exponent : Int) = .ok ((base : Int) ^ exponent)) pbtCfg

example : (List.range 12).all (fun b =>
    (List.range 8).all (fun e =>
      prog (b : Int) (e : Int) == .ok ((b : Int) ^ e))) = true := by native_decide

-- PBT for valueError_prop: every negative pair is rejected with the Python message
#eval Plausible.Testable.check
  (∀ base exponent : Nat,
    prog (-(base + 1) : Int) (exponent : Int) =
      .error (errorMsg (-(base + 1) : Int) (exponent : Int)) ∧
    prog (base : Int) (-(exponent + 1) : Int) =
      .error (errorMsg (base : Int) (-(exponent + 1) : Int)) ∧
    prog (-(base + 1) : Int) (-(exponent + 1) : Int) =
      .error (errorMsg (-(base + 1) : Int) (-(exponent + 1) : Int))) pbtCfg

example : pbtInts.all (fun b =>
    pbtInts.all (fun e =>
      pre b e || prog b e == .error (errorMsg b e))) = true := by native_decide

-- PBT for neg_base_prop
#eval Plausible.Testable.check
  (∀ base exponent : Nat,
    prog (-(base + 1) : Int) (exponent : Int) =
      .error (errorMsg (-(base + 1) : Int) (exponent : Int))) pbtCfg

example : (List.range 8).all (fun b =>
    pbtInts.all (fun e =>
      prog (-(b + 1) : Int) e == .error (errorMsg (-(b + 1) : Int) e))) = true := by native_decide

-- PBT for neg_exp_prop
#eval Plausible.Testable.check
  (∀ base exponent : Nat,
    prog (base : Int) (-(exponent + 1) : Int) =
      .error (errorMsg (base : Int) (-(exponent + 1) : Int))) pbtCfg

example : pbtInts.all (fun b =>
    (List.range 8).all (fun e =>
      prog b (-(e + 1) : Int) == .error (errorMsg b (-(e + 1) : Int)))) = true := by native_decide

-- PBT for prog_zero_exp_prop
#eval Plausible.Testable.check
  (∀ base : Nat, prog (base : Int) 0 = .ok 1) pbtCfg

example : (List.range 30).all (fun b => prog (b : Int) 0 == .ok 1) = true := by native_decide

-- PBT for prog_zero_base_prop
#eval Plausible.Testable.check
  (∀ exponent : Nat, prog 0 ((exponent + 1 : Nat) : Int) = .ok 0) pbtCfg

example : (List.range 20).all (fun e => e == 0 || prog 0 (e : Int) == .ok 0) = true := by
  native_decide

-- PBT for prog_zero_zero_prop
example : prog 0 0 == .ok 1 := by native_decide

-- PBT for bad_inputs_prop
example : (prog (-1) 2 == .error (errorMsg (-1) 2) &&
    prog 2 (-1) == .error (errorMsg 2 (-1))) = true := by native_decide

-- PBT for result_nonneg_prop
#eval Plausible.Testable.check
  (∀ base exponent : Nat,
    0 ≤ ((myPower base exponent : Nat) : Int) ∧
      prog (base : Int) (exponent : Int) = .ok (↑(myPower base exponent))) pbtCfg

example : (List.range 12).all (fun b =>
    (List.range 8).all (fun e =>
      match prog (b : Int) (e : Int) with
      | .ok n => decide (0 ≤ n)
      | .error _ => false)) = true := by native_decide

/-- Executable form of `Post_prop` on one pair. Used by the grid test below. -/
def checkPost (base exponent : Int) : Bool :=
  let r := prog base exponent
  (r == .ok (↑(myPower base.toNat exponent.toNat))) &&
  (r == .ok (base ^ exponent.toNat)) &&
  (!(exponent == 0) || r == .ok 1) &&
  (!(base == 0 && exponent == 0) || r == .ok 1) &&
  (!(base == 0 && decide (0 < exponent)) || r == .ok 0)

-- PBT for Post_prop, quantified over natural inputs (all of which satisfy `Pre`)
#eval Plausible.Testable.check
  (∀ base exponent : Nat,
    prog (base : Int) (exponent : Int) = .ok (↑(myPower base exponent)) ∧
    prog (base : Int) (exponent : Int) = .ok ((base : Int) ^ exponent) ∧
    (exponent = 0 → prog (base : Int) (exponent : Int) = .ok 1) ∧
    (base = 0 ∧ exponent = 0 → prog (base : Int) (exponent : Int) = .ok 1) ∧
    (base = 0 ∧ 0 < exponent → prog (base : Int) (exponent : Int) = .ok 0)) pbtCfg

example : pbtInts.all (fun b =>
    pbtInts.all (fun e => !(pre b e) || checkPost b e)) = true := by native_decide

/-! ## Correctness: Pre → Post -/

theorem correctness_thm (base exponent : Int) (hPre : Pre base exponent) :
    Post_prop base exponent := by
  unfold Post_prop
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact prog_ok_thm base exponent hPre
  · exact prog_math_thm base exponent hPre
  · intro hz
    subst hz
    exact prog_zero_exp_thm base hPre.1
  · intro h
    rcases h with ⟨hb, hz⟩
    subst hb hz
    exact prog_zero_zero_thm
  · intro h
    rcases h with ⟨hb, he⟩
    subst hb
    exact prog_zero_base_thm exponent he

/-! ## Imperative implementation -/

/-- Imperative translation of Python `prog`.

The `pre` check and the `exponent == 0` short-circuit match the Python control
flow. The loop is `result = 1` followed by `exponent` updates `result *= base`. -/
def progImp (base exponent : Int) : Except String Int :=
  if !pre base exponent then
    .error (errorMsg base exponent)
  else if exponent == 0 then
    .ok 1
  else
    Id.run do
      let mut result : Int := 1
      for _ in List.range exponent.toNat do
        result := result * base
      return .ok result

/-! ## Imperative tests -/

example : progImp 2 3 = .ok 8 := by native_decide
example : progImp 0 0 = .ok 1 := by native_decide
example : progImp 0 5 = .ok 0 := by native_decide
example : progImp 7 0 = .ok 1 := by native_decide
example : progImp 3 4 = .ok 81 := by native_decide
example : progImp 2 10 = .ok 1024 := by native_decide
example : progImp (-1) 2 = .error (errorMsg (-1) 2) := by native_decide
example : progImp 2 (-1) = .error (errorMsg 2 (-1)) := by native_decide
example : progImp (-3) (-1) = .error (errorMsg (-3) (-1)) := by native_decide
example : progImp (-4) 0 = .error (errorMsg (-4) 0) := by native_decide

#eval progImp 2 3
#eval progImp 0 0
#eval progImp (-1) 2
#eval progImp 2 (-1)
#eval progImp 10 3

/-! ## Equivalence: functional = imperative -/

/-- `acc * base`, repeated `n` times, as the fold performed by the imperative loop. -/
def loopMul (base : Int) (n : Nat) : Int :=
  (List.range n).foldl (fun r (_ : Nat) => r * base) 1

private theorem foldl_mul (base acc : Int) (n : Nat) :
    (List.range n).foldl (fun r (_ : Nat) => r * base) acc = acc * base ^ n := by
  induction n generalizing acc with
  | zero => simp [List.range_zero]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp [Int.pow_succ, Int.mul_assoc]

private theorem loopMul_eq_pow (base : Int) (n : Nat) : loopMul base n = base ^ n := by
  unfold loopMul
  rw [foldl_mul, Int.one_mul]

private theorem progImp_char (base exponent : Int) :
    progImp base exponent =
      if pre base exponent then
        if exponent == 0 then
          .ok 1
        else
          .ok (loopMul base exponent.toNat)
      else
        .error (errorMsg base exponent) := by
  unfold progImp loopMul
  cases pre base exponent <;> cases exponent == 0 <;>
    (dsimp [Bool.not]
     try simp only [Id.run_pure, pure_bind, List.forIn_pure_yield_eq_foldl])

/-- `prog` and `progImp` agree on every integer input, including `ValueError` cases. -/
theorem equiv_thm (base exponent : Int) : prog base exponent = progImp base exponent := by
  rw [progImp_char]
  cases hp : pre base exponent
  · simp [prog, hp]
  · have hiff := pre_iff_thm base exponent
    unfold pre_iff_prop at hiff
    have hb : 0 ≤ base := (hiff.mp hp).1
    have hcast := myPower_cast_eq_int_pow base exponent hb
    cases he : exponent == 0
    · simp [prog, hp, hcast, loopMul_eq_pow]
    · have hexp : exponent = 0 := beq_iff_eq.mp he
      subst hexp
      simp [prog, hp, myPower]

example : pbtInts.all (fun b =>
    pbtInts.all (fun e => prog b e == progImp b e)) = true := by native_decide

end «19_MyPower»
