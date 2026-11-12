import Mathlib

/-!
# 20_MySumDigits -- sum of the decimal digits of a non-negative integer

Formalization of the Python program

```python
def pre(n):  return isinstance(n, int) and n >= 0

def prog(n):
    if not pre(n):
        raise ValueError(f"Require non-negative integer (got n={n!r})")
    if n == 0:
        return 0
    total = 0
    while n > 0:
        total += n % 10
        n //= 10
    return total
```

## Modelling notes

* `digitSum : Nat -> Nat` is the functional implementation of the digit sum.  It mirrors the
  loop body `total += n % 10; n //= 10` as the recursion
  `digitSum (k+1) = (k+1) % 10 + digitSum ((k+1) / 10)` together with `digitSum 0 = 0`,
  which also covers Python's special case `if n == 0: return 0`.
* Python is dynamically typed and `pre` checks `isinstance(n, int)`.  The value handed to
  `prog` is therefore modelled by the inductive type `PyValue`: `PyValue.int n` for an `int`
  and `PyValue.float f` for a non-`int` number such as the test input `3.14`.  Consequently
  `Pre` captures *both* conjuncts of Python's `pre` (`isinstance(n, int)` and `n >= 0`).
* `prog : PyValue -> Except String Nat` returns `.error msg` exactly where Python raises
  `ValueError` (with the same message text) and `.ok (digitSum n.toNat)` otherwise.
* `digitSumImp` / `progImp` are the imperative implementations, written with `Id.run do` and
  mutable state.  Lean's `while` loop desugars to `partial def Lean.Loop.forIn`, which the
  kernel cannot unfold, so the loop is written as a fuel bounded `for` loop over
  `List.range (n + 1)`: since `m / 10 < m` whenever `0 < m`, the loop variable reaches `0`
  within `n + 1` iterations and the remaining iterations are no-ops.  This keeps the
  functional/imperative equivalence theorem kernel-checkable.
* All theorems are proved without `sorry`, `native_decide`, `partial` or new axioms;
  `native_decide` is used only inside `example` tests.
-/

namespace «20_MySumDigits»

/-! ## Python value model -/

/-- A value as Python's `prog` receives it: either an `int`, or a non-`int` number
(the Python test suite passes the float `3.14`). -/
inductive PyValue where
  | int (n : Int)
  | float (f : Float)

/-! ## Functional implementation -/

/-- Sum of the decimal digits of `n`. -/
def digitSum : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) % 10 + digitSum ((n + 1) / 10)
termination_by n => n

theorem digitSum_zero : digitSum 0 = 0 := digitSum.eq_1

theorem digitSum_succ (k : Nat) :
    digitSum (k + 1) = (k + 1) % 10 + digitSum ((k + 1) / 10) := digitSum.eq_2 k

/-- Semantics of one loop iteration; it also holds for `m = 0` (both sides are `0`). -/
theorem digitSum_rec (m : Nat) : digitSum m = m % 10 + digitSum (m / 10) := by
  rcases m with _ | k
  · rw [digitSum_zero]
  · exact digitSum_succ k

/-- The message of the `ValueError` raised by the Python program. -/
def errMsg : PyValue → String
  | .int n => s!"Require non-negative integer (got n={n})"
  | .float f => s!"Require non-negative integer (got n={f})"

/-- Core and Mathlib provide no decidable equality for `Except`, so we give one for the
result type of `prog`; it is only used by the executable tests below. -/
instance : DecidableEq (Except String Nat)
  | .ok a, .ok b =>
    if h : a = b then isTrue (by rw [h]) else isFalse (fun hc => h (Except.ok.inj hc))
  | .error e, .error f =>
    if h : e = f then isTrue (by rw [h]) else isFalse (fun hc => h (Except.error.inj hc))
  | .ok _, .error _ => isFalse (fun hc => by cases hc)
  | .error _, .ok _ => isFalse (fun hc => by cases hc)

/-- Functional implementation of Python's `prog`. -/
def prog : PyValue → Except String Nat
  | .int n => if _h : 0 ≤ n then .ok (digitSum n.toNat) else .error (errMsg (.int n))
  | .float f => .error (errMsg (.float f))

theorem prog_int_of_nonneg (n : Int) (h : 0 ≤ n) :
    prog (.int n) = .ok (digitSum n.toNat) := by
  exact dif_pos h

theorem prog_int_of_neg (n : Int) (h : n < 0) :
    prog (.int n) = .error (errMsg (.int n)) := by
  exact dif_neg (by omega)

theorem prog_float (f : Float) : prog (.float f) = .error (errMsg (.float f)) := rfl

/-! ## Unit tests (functional) -/

example : digitSum 0 = 0 := by native_decide
example : digitSum 5 = 5 := by native_decide
example : digitSum 9 = 9 := by native_decide
example : digitSum 10 = 1 := by native_decide
example : digitSum 123 = 6 := by native_decide
example : digitSum 9999 = 36 := by native_decide
example : digitSum 1000000 = 1 := by native_decide
example : prog (.int 123) = .ok 6 := by native_decide
example : prog (.int 0) = .ok 0 := by native_decide
example : (prog (.int (-1))).toOption = none := by native_decide
example : (prog (.float 3.14)).toOption = none := by native_decide
example : errMsg (.int (-1)) = "Require non-negative integer (got n=-1)" := by native_decide

#eval digitSum 123
#eval digitSum 0
#eval prog (.int 123)
#eval prog (.int 0)
#eval prog (.int (-1))
#eval prog (.float 3.14)

/-! ## Precondition -/

/-- `Pre x` is true iff `x` is a non-negative integer: it captures both
`isinstance(n, int)` and `n >= 0` of the Python `pre`. -/
def Pre : PyValue → Prop
  | .int n => 0 ≤ n
  | .float _ => False

instance : DecidablePred (@Pre)
  | .int n => (inferInstance : Decidable (0 ≤ n))
  | .float _ => isFalse (fun h => h)

/-- Executable counterpart of the Python function `pre`. -/
def preBool : PyValue → Bool
  | .int n => decide (0 ≤ n)
  | .float _ => false

theorem preBool_correct (x : PyValue) : preBool x = true ↔ Pre x := by
  cases x with
  | int n => simp [preBool, Pre]
  | float f => simp [preBool, Pre]

theorem Pre_int (n : Int) : Pre (.int n) ↔ 0 ≤ n := Iff.rfl

theorem Pre_float (f : Float) : ¬ Pre (.float f) := id

example : preBool (.int 7) = true := by native_decide
example : preBool (.int (-7)) = false := by native_decide
example : preBool (.float 3.14) = false := by native_decide
#eval preBool (.int 7)
#eval preBool (.int (-7))
#eval preBool (.float 3.14)

/-! ## Properties of the functional implementation -/

/-- Python's `if n == 0: return 0`. -/
def zero_prop : Prop := digitSum 0 = 0

theorem zero_thm : zero_prop := digitSum_zero

/-- Semantics of one loop iteration `total += n % 10; n //= 10`. -/
def rec_prop : Prop := ∀ m : Nat, digitSum m = m % 10 + digitSum (m / 10)

theorem rec_thm : rec_prop := digitSum_rec

/-- A single digit number returns itself. -/
def single_prop : Prop := ∀ d : Nat, d < 10 → digitSum d = d

theorem single_thm : single_prop := by
  intro d hd
  have hb : d ≤ 9 := by omega
  interval_cases d <;> simp [digitSum]

/-- Appending a digit `d < 10` to the right of `n` adds `d` to the digit sum. -/
def decomp_prop : Prop := ∀ n d : Nat, d < 10 → digitSum (10 * n + d) = digitSum n + d

theorem decomp_thm : decomp_prop := by
  intro n d hd
  rcases n with _ | n
  · have h1 : digitSum d = d := single_thm d hd
    have h3 : 10 * 0 + d = d := by omega
    rw [h3, h1, digitSum_zero]
    omega
  · have hpos : 0 < 10 * (n + 1) + d := by omega
    rw [digitSum_rec]
    have h1 : (10 * (n + 1) + d) % 10 = d := by omega
    have h2 : (10 * (n + 1) + d) / 10 = n + 1 := by omega
    rw [h1, h2]
    omega

/-- Appending a zero digit does not change the digit sum. -/
def mulTen_prop : Prop := ∀ n : Nat, digitSum (10 * n) = digitSum n

theorem mulTen_thm : mulTen_prop := by
  intro n
  simpa using decomp_thm n 0 (by decide)

/-- Casting out nines: the digit sum is congruent to `n` modulo 9. -/
def mod9_prop : Prop := ∀ n : Nat, digitSum n ≡ n [MOD 9]

theorem mod9_thm : mod9_prop := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n.eq_zero_or_pos with h | h
    · subst h
      rw [digitSum_zero]
    · have hlt : n / 10 < n := Nat.div_lt_self h (by decide)
      have IH := ih (n / 10) hlt
      have hstep : n % 10 + n / 10 ≡ n [MOD 9] := by
        have h1 : (n % 10 + n / 10) % 9 = n % 9 := by
          have h2 := Nat.mod_add_div n 10
          omega
        exact h1
      rw [digitSum_rec]
      exact ((Nat.ModEq.refl (n % 10)).add IH).trans hstep

/-- The digit sum never exceeds the number itself. -/
def le_prop : Prop := ∀ n : Nat, digitSum n ≤ n

theorem le_thm : le_prop := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n.eq_zero_or_pos with h | h
    · subst h
      rw [digitSum_zero]
    · have hlt : n / 10 < n := Nat.div_lt_self h (by decide)
      have IH := ih (n / 10) hlt
      have hsum : n % 10 + n / 10 ≤ n := by
        have h2 := Nat.mod_add_div n 10
        omega
      rw [digitSum_rec]
      omega

/-- A positive number has a positive digit sum. -/
def pos_prop : Prop := ∀ n : Nat, 0 < n → 0 < digitSum n

theorem pos_thm : pos_prop := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases n.eq_zero_or_pos with h | h
    · subst h
      omega
    · have hlt : n / 10 < n := Nat.div_lt_self h (by decide)
      rw [digitSum_rec]
      rcases Nat.eq_zero_or_pos (n % 10) with hm | hm
      · have hpos : 0 < n / 10 := by
          have h2 := Nat.mod_add_div n 10
          omega
        have IH := ih (n / 10) hlt hpos
        omega
      · omega

/-- The digit sum is zero exactly for zero. -/
def eqZero_prop : Prop := ∀ n : Nat, digitSum n = 0 ↔ n = 0

theorem eqZero_thm : eqZero_prop := by
  intro n
  constructor
  · intro h
    by_contra hn
    have hpos : 0 < digitSum n := pos_thm n (Nat.pos_of_ne_zero hn)
    omega
  · intro h
    subst h
    exact digitSum_zero

/-- `digitSum` agrees with the sum of Mathlib's decimal digits. -/
def digits_prop : Prop := ∀ n : Nat, digitSum n = (Nat.digits 10 n).sum

theorem digits_thm : digits_prop := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n.eq_zero_or_pos with h | h
    · subst h
      rw [digitSum_zero, Nat.digits_zero, List.sum_nil]
    · rw [digitSum_rec, Nat.digits_eq_cons_digits_div (by decide) h.ne', List.sum_cons]
      have hlt : n / 10 < n := Nat.div_lt_self h (by decide)
      rw [ih (n / 10) hlt]

/-- On admissible input `prog` returns the digit sum of `n`. -/
def ok_prop : Prop := ∀ n : Int, 0 ≤ n → prog (.int n) = .ok (digitSum n.toNat)

theorem ok_thm : ok_prop := fun n h => prog_int_of_nonneg n h

/-- A `Nat` input is always admissible, and `prog` returns its digit sum. -/
def okNat_prop : Prop := ∀ n : Nat, prog (.int (n : Int)) = .ok (digitSum n)

theorem okNat_thm : okNat_prop := by
  intro n
  have h := prog_int_of_nonneg (n : Int) (Int.ofNat_zero_le n)
  rw [Int.toNat_natCast] at h
  exact h

/-- A negative `int` violates `pre`, so `prog` raises `ValueError`. -/
def errNeg_prop : Prop := ∀ n : Int, n < 0 → ∃ e, prog (.int n) = .error e

theorem errNeg_thm : errNeg_prop := fun n hn => ⟨errMsg (.int n), prog_int_of_neg n hn⟩

/-- A non-`int` value (the Python test uses `3.14`) violates `pre`, so `prog` raises. -/
def errFloat_prop : Prop := ∀ f : Float, ∃ e, prog (.float f) = .error e

theorem errFloat_thm : errFloat_prop := fun f => ⟨errMsg (.float f), prog_float f⟩

/-- `preBool` decides `Pre`. -/
def preBool_prop : Prop := ∀ x : PyValue, preBool x = true ↔ Pre x

theorem preBool_thm : preBool_prop := preBool_correct

/-! ## Post-condition -/

/-- The value Python's `prog` returns when the pre-condition holds. -/
def expectedVal (x : PyValue) : Nat :=
  match x with
  | .int n => digitSum n.toNat
  | .float _ => 0

theorem expectedVal_int (n : Int) : expectedVal (.int n) = digitSum n.toNat := rfl

/-- Post-condition of `prog`: on admissible input it succeeds with the sum of the digits,
and on a pre-condition violation it fails with an error (Python's `ValueError`). -/
def Post_prop (x : PyValue) (r : Except String Nat) : Prop :=
  (Pre x → ∃ k, r = .ok k ∧ k = expectedVal x) ∧
  (¬ Pre x → ∃ e, r = .error e)

/-- Executable Boolean form of `Post_prop` (used by the property-based tests). -/
def isOkWith (r : Except String Nat) (k : Nat) : Bool :=
  match r with
  | .ok k' => k' == k
  | .error _ => false

def isErrorB (r : Except String Nat) : Bool :=
  match r with
  | .ok _ => false
  | .error _ => true

def postBool (x : PyValue) (r : Except String Nat) : Bool :=
  (preBool x && isOkWith r (expectedVal x)) || (!preBool x && isErrorB r)

theorem isOkWith_true (r : Except String Nat) (k : Nat) :
    isOkWith r k = true ↔ r = .ok k := by
  cases r with
  | ok k' => simp [isOkWith]
  | error e => simp [isOkWith]

theorem isErrorB_true (r : Except String Nat) :
    isErrorB r = true ↔ ∃ e, r = .error e := by
  cases r with
  | ok k => simp [isErrorB]
  | error e => simp [isErrorB]

theorem postBool_correct (x : PyValue) (r : Except String Nat) :
    postBool x r = true ↔ Post_prop x r := by
  cases x with
  | int n =>
    by_cases hn : 0 ≤ n
    · have pb : preBool (.int n) = true := by rw [preBool]; exact decide_eq_true hn
      have hsimp : postBool (.int n) r = isOkWith r (digitSum n.toNat) := by
        simp [postBool, pb, expectedVal]
      rw [hsimp, isOkWith_true]
      constructor
      · intro hr
        refine ⟨fun _ => ⟨digitSum n.toNat, hr, rfl⟩, fun hnn => absurd hn hnn⟩
      · intro hpost
        rcases hpost.1 hn with ⟨k, hk1, hk2⟩
        rw [hk2] at hk1
        exact hk1
    · have pb : preBool (.int n) = false := by rw [preBool]; exact decide_eq_false hn
      have hsimp : postBool (.int n) r = isErrorB r := by simp [postBool, pb]
      rw [hsimp, isErrorB_true]
      constructor
      · intro hr
        exact ⟨fun hpre => absurd hpre hn, fun _ => hr⟩
      · intro hpost
        exact hpost.2 hn
  | float f =>
    have pb : preBool (.float f) = false := rfl
    have hsimp : postBool (.float f) r = isErrorB r := by simp [postBool, pb]
    rw [hsimp, isErrorB_true]
    constructor
    · intro hr
      exact ⟨fun hpre => absurd hpre (Pre_float f), fun _ => hr⟩
    · intro hpost
      exact hpost.2 (Pre_float f)

/-- `prog` always satisfies its post-condition. -/
theorem prog_spec (x : PyValue) : Post_prop x (prog x) := by
  cases x with
  | int n =>
    by_cases hn : 0 ≤ n
    · refine ⟨fun _ => ⟨digitSum n.toNat, prog_int_of_nonneg n hn, rfl⟩,
        fun hnn => absurd hn hnn⟩
    · refine ⟨fun hpre => absurd hpre hn,
        fun _ => ⟨errMsg (.int n), prog_int_of_neg n (by omega)⟩⟩
  | float f =>
    refine ⟨fun hpre => absurd hpre (Pre_float f),
      fun _ => ⟨errMsg (.float f), prog_float f⟩⟩

/-- Correctness of `prog`: the pre-condition implies the post-condition. -/
def correctness_prop : Prop := ∀ x : PyValue, Pre x → Post_prop x (prog x)

theorem correctness_thm : correctness_prop := fun x _ => prog_spec x

/-- The post-condition holds for every input, admissible or not. -/
def spec_prop : Prop := ∀ x : PyValue, Post_prop x (prog x)

theorem spec_thm : spec_prop := prog_spec

/-! ## Property-based tests

Randomized PBTs use `Plausible.Testable.check` (Plausible ships with Mathlib): the file fails
to compile if a counterexample is found.  Bounded PBTs exhaustively check small inputs with
`native_decide`.  Every executable property stated above is tested here.  Side conditions
such as `d < 10` are enforced with `d % 10` (and additionally by an exhaustive bounded test)
so that Plausible does not have to "give up" on unsatisfied preconditions.
-/

-- PBT for `zero_prop`
example : zero_prop := by
  show digitSum 0 = 0
  native_decide

-- PBT for `rec_prop`
#eval Plausible.Testable.check (∀ m : Nat, digitSum m = m % 10 + digitSum (m / 10))
example : (List.range 2000).all (fun m => digitSum m = m % 10 + digitSum (m / 10)) = true := by
  native_decide

-- PBT for `single_prop` (the domain `d < 10` is finite: exhaustive bounded test)
example : (List.range 10).all (fun d => digitSum d = d) = true := by native_decide
#eval Plausible.Testable.check (∀ d : Nat, digitSum (d % 10) = d % 10)

-- PBT for `decomp_prop`
#eval Plausible.Testable.check (∀ n d : Nat, digitSum (10 * n + d % 10) = digitSum n + d % 10)
example : (List.range 200).all
    (fun n => (List.range 10).all (fun d => digitSum (10 * n + d) = digitSum n + d)) = true := by
  native_decide

-- PBT for `mulTen_prop`
#eval Plausible.Testable.check (∀ n : Nat, digitSum (10 * n) = digitSum n)
example : (List.range 2000).all (fun n => digitSum (10 * n) = digitSum n) = true := by
  native_decide

-- PBT for `mod9_prop`
#eval Plausible.Testable.check (∀ n : Nat, digitSum n % 9 = n % 9)
example : (List.range 5000).all (fun n => digitSum n % 9 = n % 9) = true := by native_decide

-- PBT for `le_prop`
#eval Plausible.Testable.check (∀ n : Nat, digitSum n ≤ n)
example : (List.range 5000).all (fun n => digitSum n ≤ n) = true := by native_decide

-- PBT for `pos_prop`
#eval Plausible.Testable.check (∀ n : Nat, 0 < digitSum (n + 1))
example : (List.range 5000).all (fun n => decide (n = 0 ∨ 0 < digitSum n)) = true := by
  native_decide

-- PBT for `eqZero_prop`
#eval Plausible.Testable.check (∀ n : Nat, digitSum n = 0 ↔ n = 0)
example : (List.range 5000).all (fun n => decide ((digitSum n = 0) ↔ (n = 0))) = true := by
  native_decide

-- PBT for `digits_prop`
#eval Plausible.Testable.check (∀ n : Nat, digitSum n = (Nat.digits 10 n).sum)
example : (List.range 2000).all (fun n => digitSum n = (Nat.digits 10 n).sum) = true := by
  native_decide

-- PBT for `ok_prop`
#eval Plausible.Testable.check (∀ n : Nat, prog (.int (n : Int)) = .ok (digitSum n))
#eval Plausible.Testable.check (∀ n : Int,
    prog (.int n) = if 0 ≤ n then Except.ok (digitSum n.toNat) else Except.error (errMsg (.int n)))
example : (List.range 1000).all (fun n => prog (.int (n : Int)) = .ok (digitSum n)) = true := by
  native_decide

-- PBT for `errNeg_prop`
#eval Plausible.Testable.check (∀ n : Nat, (prog (.int (-((n : Int) + 1)))).toOption = none)
example : ((List.range 100).map (fun i => -((i : Int) + 1))).all
    (fun n => (prog (.int n)).toOption = none) = true := by native_decide

-- PBT for `errFloat_prop`
example : ([3.14, -0.5, 0.0, 1e9, -2.718281828]).all
    (fun f => isErrorB (prog (.float f))) = true := by native_decide

-- PBT for `preBool_prop`
example : ((List.range 41).map (fun i => (i : Int) - 20)).all
    (fun n => preBool (.int n) = decide (0 ≤ n)) = true := by native_decide
example : ([3.14, -0.5, 0.0]).all (fun f => preBool (.float f) = false) = true := by
  native_decide

-- PBT for `Post_prop` (via its executable Boolean form `postBool`, see `postBool_correct`)
#eval Plausible.Testable.check (∀ n : Int, postBool (.int n) (prog (.int n)))
example : (List.range 300).all (fun n => postBool (.int n) (prog (.int n))) = true := by
  native_decide
example : ((List.range 201).map (fun i => (i : Int) - 100)).all
    (fun n => postBool (.int n) (prog (.int n))) = true := by native_decide
example : ([PyValue.float 3.14, PyValue.float (-0.5), PyValue.float 0.0, PyValue.float 1e9]).all
    (fun x => postBool x (prog x)) = true := by native_decide

/-! ## Imperative implementation

`Id.run do` with mutable state, mirroring the Python `while n > 0` loop.
-/

/-- One iteration of the imperative loop, acting on the state `(m, total)`. -/
def loopStep (s : MProd Nat Nat) : MProd Nat Nat := ⟨s.fst / 10, s.snd + s.fst % 10⟩

/-- `iterG k g a` applies `g` to `a` exactly `k` times. -/
def iterG {α : Type} : Nat → (α → α) → α → α
  | 0, _, a => a
  | n + 1, g, a => g (iterG n g a)

/-- Imperative digit sum: mutable `total` and `m`, exactly as in the Python `while` loop.
The `for` loop supplies the fuel `n + 1`, which is enough because `m / 10 < m` for `0 < m`;
the extra iterations only add `0 % 10 = 0` and leave the state unchanged. -/
def digitSumImp (n : Nat) : Nat := Id.run do
  let mut m := n
  let mut total := 0
  for _ in List.range (n + 1) do
    total := total + m % 10
    m := m / 10
  return total

/-- Imperative version of Python's `prog`: it checks the pre-condition and then runs the
mutable loop above. -/
def progImp (x : PyValue) : Except String Nat := Id.run do
  match x with
  | .int n =>
    if n < 0 then
      return .error (errMsg (.int n))
    else
      let mut m := n.toNat
      let mut total := 0
      for _ in List.range (n.toNat + 1) do
        total := total + m % 10
        m := m / 10
      return .ok total
  | .float f =>
    return .error (errMsg (.float f))

theorem digitSumImp_foldl (n : Nat) :
    digitSumImp n = ((List.range (n + 1)).foldl (fun b _ => loopStep b) ⟨n, 0⟩).snd := by
  simp [digitSumImp, loopStep]

theorem foldl_range_iterG {α : Type} (g : α → α) (a : α) : ∀ n : Nat,
    (List.range n).foldl (fun x _ => g x) a = iterG n g a := by
  intro n
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, iterG]
    rw [ih]

theorem digitSumImp_eq_iterG (n : Nat) :
    digitSumImp n = (iterG (n + 1) loopStep ⟨n, 0⟩).snd := by
  rw [digitSumImp_foldl, foldl_range_iterG]

/-- Loop invariant: `digitSum m + total` is preserved by every iteration. -/
theorem iterG_invariant : ∀ k (s : MProd Nat Nat),
    digitSum (iterG k loopStep s).fst + (iterG k loopStep s).snd = digitSum s.fst + s.snd := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    have h1 := ih s
    have h2 := digitSum_rec (iterG k loopStep s).fst
    have h3 : (loopStep (iterG k loopStep s)).fst = (iterG k loopStep s).fst / 10 := rfl
    have h4 : (loopStep (iterG k loopStep s)).snd =
        (iterG k loopStep s).snd + (iterG k loopStep s).fst % 10 := rfl
    show digitSum (loopStep (iterG k loopStep s)).fst + (loopStep (iterG k loopStep s)).snd =
        digitSum s.fst + s.snd
    rw [h3, h4]
    omega

theorem div10_le : ∀ u : Nat, u / 10 = 0 ∨ u / 10 + 1 ≤ u := by
  intro u
  rcases u with _ | m
  · left; rfl
  · right
    have := Nat.div_lt_self (Nat.succ_pos m) (by decide : 1 < 10)
    omega

/-- The fuel `n + 1` suffices: after that many iterations the loop variable is `0`. -/
theorem iterG_fuel : ∀ k (s : MProd Nat Nat),
    (iterG k loopStep s).fst = 0 ∨ (iterG k loopStep s).fst + k ≤ s.fst := by
  intro k
  induction k with
  | zero => intro s; right; rfl
  | succ k ih =>
    intro s
    have h := ih s
    have h1 : (iterG (k + 1) loopStep s).fst = (iterG k loopStep s).fst / 10 := by
      show (loopStep (iterG k loopStep s)).fst = (iterG k loopStep s).fst / 10
      rfl
    have hdiv := div10_le (iterG k loopStep s).fst
    rw [h1]
    rcases h with hz | hz
    · rcases hdiv with hd | hd
      · left; exact hd
      · omega
    · rcases hdiv with hd | hd
      · left; exact hd
      · right; omega

theorem digitSumImp_eq_digitSum (n : Nat) : digitSumImp n = digitSum n := by
  have h1 := iterG_invariant (n + 1) ⟨n, 0⟩
  have h2 := iterG_fuel (n + 1) ⟨n, 0⟩
  have h3 : (iterG (n + 1) loopStep ⟨n, 0⟩).fst = 0 := by
    rcases h2 with h | h
    · exact h
    · simp at h
      omega
  simp only [h3, digitSum_zero] at h1
  simp at h1
  rw [digitSumImp_eq_iterG]
  omega

theorem progImp_int_of_nonneg (n : Int) (h : 0 ≤ n) :
    progImp (.int n) = .ok (digitSumImp n.toNat) := by
  have hnl : ¬(n < 0) := by omega
  simp [progImp, digitSumImp, hnl]

theorem progImp_int_of_neg (n : Int) (h : n < 0) :
    progImp (.int n) = .error (errMsg (.int n)) := by
  simp [progImp, h]

theorem progImp_float (f : Float) :
    progImp (.float f) = .error (errMsg (.float f)) := by
  simp [progImp]

/-! ## Imperative tests -/

example : digitSumImp 123 = 6 := by native_decide
example : digitSumImp 0 = 0 := by native_decide
example : digitSumImp 9999 = 36 := by native_decide
example : digitSumImp 1000000 = 1 := by native_decide
example : progImp (.int 123) = .ok 6 := by native_decide
example : progImp (.int 0) = .ok 0 := by native_decide
example : (progImp (.int (-1))).toOption = none := by native_decide
example : (progImp (.float 3.14)).toOption = none := by native_decide
example : (List.range 1000).all (fun n => digitSumImp n = digitSum n) = true := by native_decide
example : (List.range 500).all (fun n => postBool (.int n) (progImp (.int n))) = true := by
  native_decide

#eval digitSumImp 123
#eval digitSumImp 0
#eval digitSumImp 12345
#eval progImp (.int 123)
#eval progImp (.int 0)
#eval progImp (.int (-1))
#eval progImp (.float 3.14)

/-! ## Equivalence of the functional and the imperative implementation -/

def equivNat_prop : Prop := ∀ n : Nat, digitSum n = digitSumImp n

theorem equivNat_thm : equivNat_prop := fun n => (digitSumImp_eq_digitSum n).symm

def equiv_prop : Prop := ∀ x : PyValue, prog x = progImp x

theorem equiv_thm : equiv_prop := by
  intro x
  cases x with
  | int n =>
    by_cases h : 0 ≤ n
    · rw [prog_int_of_nonneg n h, progImp_int_of_nonneg n h, digitSumImp_eq_digitSum]
    · have hn : n < 0 := by omega
      rw [prog_int_of_neg n hn, progImp_int_of_neg n hn]
  | float f => rw [prog_float, progImp_float]

/-- The imperative implementation satisfies the same post-condition. -/
theorem progImp_spec (x : PyValue) : Post_prop x (progImp x) := by
  have h := equiv_thm x
  rw [← h]
  exact prog_spec x

def impCorrect_prop : Prop := ∀ x : PyValue, Pre x → Post_prop x (progImp x)

theorem impCorrect_thm : impCorrect_prop := fun x _ => progImp_spec x

-- PBTs for the equivalence.  The imperative loop is fuel bounded by `List.range (n + 1)`,
-- so it performs `n + 1` iterations; the randomized tests therefore restrict the sampled
-- input to a bounded range (`n % 300`, `n % 2000 - 1000`), and the exhaustive bounded tests
-- below cover every small input, including negative ones.
#eval Plausible.Testable.check (∀ n : Nat, digitSumImp (n % 300) = digitSum (n % 300))
#eval Plausible.Testable.check (∀ n : Int,
  progImp (.int (n % 2000 - 1000)) = prog (.int (n % 2000 - 1000)))
#eval Plausible.Testable.check (∀ n : Int,
  postBool (.int (n % 2000 - 1000)) (progImp (.int (n % 2000 - 1000))))
example : (List.range 1000).all (fun n => progImp (.int n) = prog (.int n)) = true := by
  native_decide
example : ((List.range 201).map (fun i => (i : Int) - 100)).all
    (fun n => progImp (.int n) = prog (.int n)) = true := by native_decide
example : ([PyValue.float 3.14, PyValue.float (-0.5), PyValue.float 0.0]).all
    (fun x => progImp x = prog x) = true := by native_decide
example : (List.range 1000).all (fun n => digitSumImp n = (Nat.digits 10 n).sum) = true := by
  native_decide

#print axioms zero_thm
#print axioms rec_thm
#print axioms single_thm
#print axioms decomp_thm
#print axioms mulTen_thm
#print axioms mod9_thm
#print axioms le_thm
#print axioms pos_thm
#print axioms eqZero_thm
#print axioms digits_thm
#print axioms ok_thm
#print axioms okNat_thm
#print axioms errNeg_thm
#print axioms errFloat_thm
#print axioms preBool_thm
#print axioms postBool_correct
#print axioms correctness_thm
#print axioms spec_thm
#print axioms equivNat_thm
#print axioms equiv_thm
#print axioms progImp_spec
#print axioms impCorrect_thm

end «20_MySumDigits»
